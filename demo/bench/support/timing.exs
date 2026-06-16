# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifBench.Timing do
  @moduledoc """
  Minimal dependency-free timing: run `fun` `n` times, return mean/p50/p99 in us.
  A warm-up tenth is discarded so JIT/instance-warm effects don't skew the mean.
  Swap for :benchee on the OTP-28 target if richer stats are wanted; the returned
  map keys (:mean_us, :p50_us, :p99_us) are deliberately benchee-shaped.
  """
  def measure(n, fun) when n > 0 do
    warm = max(div(n, 10), 1)
    for _ <- 1..warm, do: fun.()

    samples =
      for _ <- 1..n do
        {us, _} = :timer.tc(fun)
        us
      end
      |> Enum.sort()

    %{
      mean_us: Enum.sum(samples) / n,
      p50_us: pct(samples, 0.50),
      p99_us: pct(samples, 0.99),
      n: n
    }
  end

  defp pct(sorted, q) do
    idx = min(round(q * length(sorted)), length(sorted) - 1)
    Enum.at(sorted, idx) * 1.0
  end
end
