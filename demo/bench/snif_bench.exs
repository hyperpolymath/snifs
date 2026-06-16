# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# snif_bench.exs — the [OTP28] half of the SNIF evaluation.
#
# Produces the rows the wasmtime-CLI harness (benches/snif_eval.sh) CANNOT,
# because they need the real BEAM + wasmex marshalling:
#
#   (c) per-call (ADR-003 Loader) vs pooled (ADR-004 Snif.Pool) instantiation
#   (d) SNIF (wasmex) vs raw rustler NIF vs OS Port — overhead spectrum
#   buffer round-trip: alloc -> write linear memory -> sum_f32 -> read back
#   process-survival witness: the caller pid is alive() after every trap
#
# WHY THIS IS NOT RUN IN THIS ENV: the demo targets OTP 28.3 / Elixir 1.19.4.
# This box is OTP 25 and CANNOT run wasmex. Run on the OTP-28 target with:
#
#     cd demo && mix deps.get && mix run bench/snif_bench.exs
#
# Timing uses :timer.tc (no extra dep). If :benchee is added it can replace the
# hand-rolled percentiles; the table shape below is benchee-compatible.
#
# The discriminating assertions for THIS file live inline as `expect/3` calls:
# the bench FAILS (System.halt(1)) if the pooled path is not faster than per-call,
# or if any trap kills the caller, or if the buffer round-trip is wrong.

Code.require_file("support/timing.exs", __DIR__)
alias SnifBench.Timing

priv = Path.join([__DIR__, "..", "..", "priv"])
safe = Path.join(priv, "safe_nif_ReleaseSafe.wasm")
rust = Path.join(priv, "demo_guest_rust.wasm")

n_calls = String.to_integer(System.get_env("N", "2000"))
fib_arg = 20

# ── (c) per-call (ADR-003) vs pooled (ADR-004) ────────────────────────────────
# Per-call: SnifDemo.Loader.call/3 — read+compile+instantiate EACH call.
percall = Timing.measure(n_calls, fn ->
  {:ok, [_]} = SnifDemo.Loader.call(safe, "fibonacci", [fib_arg])
end)

# Pooled: warm the pool ONCE, then call — compile-once, re-instantiate-per-call.
case Snif.Pool.start_pool(SnifDemo.SafeNif, pool_size: 4) do
  {:ok, _} -> :ok
  {:error, {:already_started, _}} -> :ok  # the app supervisor already started it
end
pooled = Timing.measure(n_calls, fn ->
  {:ok, [_]} = Snif.call(SnifDemo.SafeNif, "fibonacci", [fib_arg])
end)

# ── buffer round-trip (the audit's "THE enabler" — Rust (ptr,len) ABI) ────────
# This is the case the wasmtime CLI cannot do: write a payload INTO linear
# memory between calls. Measured + checked for correctness.
{:ok, rpid} = Wasmex.start_link(%{bytes: File.read!(rust)})
{:ok, store} = Wasmex.store(rpid)
{:ok, mem}   = Wasmex.memory(rpid)
payload = [1.0, 2.0, 3.0, 4.0, 5.0]
{:ok, [ptr]} = Wasmex.call_function(rpid, "snif_alloc", [length(payload) * 4])
Enum.with_index(payload, fn v, i ->
  # write the f32 directly as little-endian bytes (wasm32 linear memory is LE).
  # (the prior <<bits::32>> round-trip read big-endian then wrote little-endian,
  #  byte-swapping every float so sum_f32 read garbage.)
  Wasmex.Memory.write_binary(store, mem, ptr + i * 4, <<v::float-32-little>>)
end)
buf = Timing.measure(div(n_calls, 10), fn ->
  {:ok, [sum]} = Wasmex.call_function(rpid, "sum_f32", [ptr, length(payload)])
  ^sum = 15.0
end)
{:ok, [sum]} = Wasmex.call_function(rpid, "sum_f32", [ptr, length(payload)])

# ── (d) overhead spectrum: SNIF vs Port (raw rustler row is [needs-rustler]) ──
# Port: spawn an OS process that computes fibonacci. Establishes the SLOW end of
# the spectrum (process round-trip) so SNIF's number is bracketed:
#   raw rustler NIF (ns, unsandboxed) << SNIF pooled (us) << SNIF per-call << Port (us-ms)
port_row =
  case System.find_executable("awk") do
    nil -> %{mean_us: nil, note: "no awk; Port row skipped"}
    awk ->
      Timing.measure(min(n_calls, 200), fn ->
        {out, 0} = System.cmd(awk, ["BEGIN{a=0;b=1;for(i=2;i<=#{fib_arg};i++){t=a+b;a=b;b=t};print b}"])
        _ = out
      end)
  end

# ── survival witness over every crash mode (the real isolation claim) ─────────
survival =
  for fn_name <- ~w(crash_oob crash_panic crash_overflow crash_div_zero) do
    {:error, _} = Snif.call(SnifDemo.SafeNif, fn_name, [])
    {:ok, [42]} = Snif.call(SnifDemo.SafeNif, "still_alive", [])  # caller still serves
    self_alive = Process.alive?(self())
    {fn_name, self_alive}
  end

# ── TABLE ─────────────────────────────────────────────────────────────────────
IO.puts("\n== SNIF overhead table (OTP #{System.otp_release()}, n=#{n_calls}) ==")
:io.format("~-28s ~10s ~10s ~10s~n", ["case", "mean_us", "p50_us", "p99_us"])
for {name, m} <- [
      {"per-call (ADR-003 Loader)", percall},
      {"pooled   (ADR-004 Pool)", pooled},
      {"buffer round-trip sum_f32", buf},
      {"Port (awk fib)", port_row}
    ] do
  :io.format("~-28s ~10.2f ~10.2f ~10.2f~n",
    [name, m[:mean_us] || 0.0, m[:p50_us] || 0.0, m[:p99_us] || 0.0])
end

speedup = (percall[:mean_us] || 0) / max(pooled[:mean_us] || 1, 1.0e-9)
IO.puts("\npooled speedup over per-call: #{Float.round(speedup, 1)}x")
IO.puts("buffer sum_f32([1..5]) = #{sum} (expect 15.0)")
IO.puts("survival witness: #{inspect(survival)}")

# ── DISCRIMINATING ASSERTIONS (fail loud) ─────────────────────────────────────
fail = fn msg -> IO.puts(:stderr, "ASSERT-FAIL: #{msg}"); Process.put(:fails, (Process.get(:fails) || 0) + 1) end

if speedup < 2.0, do: fail.("pooled must be >=2x faster than per-call, got #{speedup}x")
if sum != 15.0, do: fail.("buffer round-trip wrong: #{sum} != 15.0")
unless Enum.all?(survival, fn {_, alive} -> alive end),
  do: fail.("caller process died on some crash mode: #{inspect(survival)}")

case Process.get(:fails) do
  nil -> IO.puts("\nall [OTP28] discriminating assertions hold"); System.halt(0)
  k   -> IO.puts(:stderr, "\n#{k} assertion failure(s)"); System.halt(1)
end
