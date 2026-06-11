# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule ProtocolSquisher.Explorer.MixProject do
  use Mix.Project

  def project do
    [
      app: :protocol_squisher_explorer,
      version: "1.1.0",
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger, :inets, :ssl, :crypto],
      mod: {ProtocolSquisher.Explorer.Application, []}
    ]
  end

  defp deps do
    []
  end
end
