defmodule Mix.Tasks.Crawler.Pattern.Extract do
  @shortdoc "Extract synthesis patterns from crawler empirical database"

  @moduledoc """
  Reads crawler `summary.json`, extracts empirical synthesis hints, and writes
  `synthesis-hints.json` for optimizer consumption.
  """

  use Mix.Task

  alias ProtocolSquisher.Explorer.PatternExtractor

  @switches [
    database_path: :string,
    summary: :string,
    output: :string,
    help: :boolean
  ]

  @impl Mix.Task
  def run(argv) do
    {opts, _args, invalid} = OptionParser.parse(argv, strict: @switches)

    if invalid != [] do
      Mix.raise("invalid options: #{inspect(invalid)}")
    end

    if opts[:help] do
      print_help()
    else
      summary_path = resolve_summary_path(opts)
      output_path = resolve_output_path(opts, summary_path)

      case PatternExtractor.extract(summary_path, output_path) do
        {:ok, hints} ->
          Mix.shell().info("wrote synthesis hints:")
          Mix.shell().info("  input_summary: #{summary_path}")
          Mix.shell().info("  output: #{output_path}")
          Mix.shell().info("  records: #{hints["record_count"]}")
          Mix.shell().info("  notes: #{length(hints["notes"] || [])}")

        {:error, reason} ->
          Mix.raise("pattern extraction failed: #{inspect(reason)}")
      end
    end
  end

  defp resolve_summary_path(opts) do
    cond do
      is_binary(opts[:summary]) ->
        opts[:summary]

      is_binary(opts[:database_path]) ->
        Path.join(opts[:database_path], "summary.json")

      true ->
        Path.expand("../../target/explorer/database/summary.json", File.cwd!())
    end
  end

  defp resolve_output_path(opts, summary_path) do
    cond do
      is_binary(opts[:output]) ->
        opts[:output]

      is_binary(opts[:database_path]) ->
        Path.join(opts[:database_path], "synthesis-hints.json")

      true ->
        Path.join(Path.dirname(summary_path), "synthesis-hints.json")
    end
  end

  defp print_help do
    Mix.shell().info("""
    Usage:
      mix crawler.pattern.extract [options]

    Options:
      --database-path <path>         Database directory (expects summary.json)
      --summary <path>               Explicit summary.json path
      --output <path>                Output hints JSON path
      --help                         Show this message
    """)
  end
end
