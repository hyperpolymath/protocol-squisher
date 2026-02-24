defmodule Mix.Tasks.Crawler.Db.Report do
  @shortdoc "Print empirical compatibility database summary"

  @moduledoc """
  Reads the crawler empirical database summary JSON and prints a human-readable
  report.
  """

  use Mix.Task

  @switches [
    database_path: :string,
    summary: :string,
    top_repos: :integer,
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

      summary =
        summary_path
        |> File.read!()
        |> :json.decode()

      top_repos = max(opts[:top_repos] || 10, 1)

      Mix.shell().info("Empirical Compatibility Database")
      Mix.shell().info("  summary: #{summary_path}")
      Mix.shell().info("  records: #{summary["total_records"]}")
      Mix.shell().info("  parse_errors: #{summary["parse_errors"]}")
      Mix.shell().info("  corpus_errors: #{summary["corpus_errors"]}")
      Mix.shell().info("  average_entity_count: #{summary["average_entity_count"]}")
      Mix.shell().info("")

      Mix.shell().info("  format_counts:")
      print_count_map(summary["format_counts"] || %{}, "    ")
      Mix.shell().info("")

      Mix.shell().info("  transport_class_counts:")
      print_count_map(summary["transport_class_counts"] || %{}, "    ")
      Mix.shell().info("")

      Mix.shell().info("  top_repositories:")

      summary["repository_counts"]
      |> top_counts(top_repos)
      |> Enum.each(fn {repo, count} ->
        Mix.shell().info("    #{repo}: #{count}")
      end)
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

  defp print_count_map(map, prefix) when is_map(map) do
    map
    |> Enum.sort_by(fn {_k, v} -> -v end)
    |> Enum.each(fn {k, v} ->
      Mix.shell().info("#{prefix}#{k}: #{v}")
    end)
  end

  defp top_counts(map, n) when is_map(map) do
    map
    |> Enum.sort_by(fn {_k, v} -> -v end)
    |> Enum.take(n)
  end

  defp print_help do
    Mix.shell().info("""
    Usage:
      mix crawler.db.report [options]

    Options:
      --database-path <path>         Database directory (expects summary.json)
      --summary <path>               Explicit summary.json path
      --top-repos <n>                Number of repositories to list (default: 10)
      --help                         Show this message
    """)
  end
end
