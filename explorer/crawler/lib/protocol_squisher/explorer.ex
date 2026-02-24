defmodule ProtocolSquisher.Explorer do
  @moduledoc """
  Entry point for the Protocol Squisher GitHub schema crawler.
  """

  alias ProtocolSquisher.Explorer.{Config, Crawler}

  @spec run(keyword()) :: {:ok, map()} | {:error, term()}
  def run(opts \\ []) do
    opts
    |> Config.from_cli()
    |> Crawler.run()
  end
end
