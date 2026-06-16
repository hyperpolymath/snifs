# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifMetamorphicTest do
  @moduledoc """
  GAP-1b — BEHAVIOUR faithfulness gate (the deeper half of model<->code).

  The Idris2 ABI proofs + `abi_conformance.py` establish that the built wasm's
  SIGNATURES match the verified model. They do NOT establish that the code
  BEHAVES as a `fibonacci` / `checked_add` actually should. This gate closes a
  slice of that with dependency-free METAMORPHIC relations: properties that must
  hold BETWEEN the outputs of related inputs, evaluated against the REAL wasm
  through the SNIF boundary. A guest with the right signature but the wrong
  kernel (e.g. addition that wraps instead of trapping, or a "fib" that is not
  fib) fails these even though it passes the interface gate.

  No StreamData / no property-test dependency: fixed, deterministic input
  families, so this runs in any CI with only the demo deps.
  """
  use ExUnit.Case, async: false
  alias SnifDemo.Loader

  @safe Path.join([__DIR__, "..", "..", "priv", "safe_nif_ReleaseSafe.wasm"])

  @i32_max 2_147_483_647
  @i32_min -2_147_483_648

  # Unwrap a successful scalar SNIF result; flunk loudly on an unexpected shape.
  defp val!(fun, args) do
    case Loader.call(@safe, fun, args) do
      {:ok, [v]} -> v
      other -> flunk("#{fun}(#{inspect(args)}) expected {:ok,[v]}, got #{inspect(other)}")
    end
  end

  # ── fibonacci: the kernel must satisfy the Fibonacci recurrence ──────────────

  test "fibonacci base cases: fib(0)=0, fib(1)=1" do
    assert val!("fibonacci", [0]) == 0
    assert val!("fibonacci", [1]) == 1
  end

  test "fibonacci METAMORPHIC recurrence: fib(n) = fib(n-1) + fib(n-2), n=2..40" do
    # The relation is between the wasm's OWN outputs for n, n-1, n-2 — not against
    # a hard-coded table. A kernel computing anything other than fib breaks it.
    fib = fn n -> val!("fibonacci", [n]) end

    Enum.each(2..40, fn n ->
      assert fib.(n) == fib.(n - 1) + fib.(n - 2),
             "recurrence broken at n=#{n}: #{fib.(n)} != #{fib.(n - 1)} + #{fib.(n - 2)}"
    end)
  end

  test "fibonacci METAMORPHIC monotonicity: fib(n+1) >= fib(n), n=1..40" do
    Enum.each(1..40, fn n ->
      assert val!("fibonacci", [n + 1]) >= val!("fibonacci", [n])
    end)
  end

  test "fibonacci uses i64 width: fib(46)=1836311903 exceeds i32 range, returned intact" do
    # fib(46) = 1_836_311_903 > i32_max would wrap/overflow a 32-bit kernel.
    # Its presence intact is evidence the return really is i64 (matches the ABI model).
    assert val!("fibonacci", [46]) == 1_836_311_903
  end

  # ── checked_add: a genuinely CHECKED i32 add — overflow TRAPS (see zig/src/safe_nif.zig) ──
  #
  # The guest computes a + b via `@addWithOverflow` and hits `unreachable` on overflow, so an
  # overflowing call FAULTS (-> {:error, _}, BEAM survives) instead of returning a value; a
  # non-overflowing call returns the exact sum. (History: this export was a wrapping `a +% b`
  # despite its name — the misnomer this gate originally surfaced — and was then made genuinely
  # checked, the behaviour the name promises. See PROOF-STATUS GAP-1b.)

  # Does a + b overflow signed i32? (arbitrary-precision host-side oracle.)
  defp overflows_i32?(a, b), do: a + b > @i32_max or a + b < @i32_min

  test "checked_add METAMORPHIC commutativity on non-overflowing pairs: add(a,b) = add(b,a)" do
    pairs = [{1, 2}, {-5, 9}, {1000, 24}, {-7, -8}, {@i32_max - 3, 2}, {@i32_min + 3, -2}]

    Enum.each(pairs, fn {a, b} ->
      refute overflows_i32?(a, b), "test pair (#{a},#{b}) must not overflow"
      assert val!("checked_add", [a, b]) == val!("checked_add", [b, a]),
             "commutativity broken at (#{a},#{b})"
    end)
  end

  test "checked_add METAMORPHIC identity: add(a,0) = a and add(0,a) = a (adding 0 never overflows)" do
    Enum.each([0, 1, -1, 42, -42, @i32_max, @i32_min], fn a ->
      assert val!("checked_add", [a, 0]) == a
      assert val!("checked_add", [0, a]) == a
    end)
  end

  test "checked_add METAMORPHIC associativity where no intermediate overflows" do
    triples = [{1, 2, 3}, {-4, 5, -6}, {100, 200, 300}, {-1, -1, -1}]

    Enum.each(triples, fn {a, b, c} ->
      left = val!("checked_add", [val!("checked_add", [a, b]), c])
      right = val!("checked_add", [a, val!("checked_add", [b, c])])
      assert left == right, "associativity broken at (#{a},#{b},#{c})"
    end)
  end

  test "checked_add is CHECKED: overflow at the boundary TRAPS (BEAM survives); just-below does not" do
    # The defining behaviour: i32_max + 1 and i32_min + (-1) FAULT, they do not wrap.
    assert {:error, _} = Loader.call(@safe, "checked_add", [@i32_max, 1])
    assert {:error, _} = Loader.call(@safe, "checked_add", [@i32_min, -1])
    assert {:error, _} = Loader.call(@safe, "checked_add", [@i32_max, @i32_max])
    # ...one short of the boundary is fine (so it is not "always traps").
    assert val!("checked_add", [@i32_max - 1, 1]) == @i32_max
    assert val!("checked_add", [@i32_min + 1, -1]) == @i32_min
    # ...and the boundary trap did not take the BEAM with it.
    assert val!("still_alive", []) == 42
  end

  test "checked_add ORACLE: non-overflow = exact sum; overflow = {:error,_}, over a boundary family" do
    family = [-3, -1, 0, 1, 3, @i32_max - 1, @i32_max, @i32_min, @i32_min + 1, 1_000_000_000]

    for a <- family, b <- family do
      if overflows_i32?(a, b) do
        assert {:error, _} = Loader.call(@safe, "checked_add", [a, b]),
               "expected a trap on overflow at (#{a},#{b})"
      else
        assert val!("checked_add", [a, b]) == a + b,
               "expected the exact sum at (#{a},#{b})"
      end
    end
  end
end
