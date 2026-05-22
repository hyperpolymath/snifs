# SPDX-License-Identifier: MPL-2.0
defmodule SnifDemo.MixProject do
  use Mix.Project

  def project do
    [
      app: :snif_demo,
      version: "0.1.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    [
      {:wasmex, "~> 0.14"}
    ]
  end
end
