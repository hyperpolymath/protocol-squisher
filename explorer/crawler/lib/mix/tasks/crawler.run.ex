defmodule Mix.Tasks.Crawler.Run do
  @shortdoc "Run the Protocol Squisher GitHub schema crawler"

  @moduledoc """
  Run the Elixir OTP crawler that discovers schema files on GitHub and stores
  NDJSON output for downstream analysis.

  Examples:

      mix crawler.run
      mix crawler.run --max-pages 1 --query 'extension:proto "syntax ="'
      mix crawler.run --with-corpus --corpus-cli ../../target/debug/protocol-squisher
  """

  use Mix.Task

  alias ProtocolSquisher.Explorer.{Config, Crawler}

  @switches [
    token: :string,
    output: :string,
    query: :keep,
    max_pages: :integer,
    per_page: :integer,
    concurrency: :integer,
    parser_concurrency: :integer,
    request_timeout_ms: :integer,
    parse_timeout_ms: :integer,
    sleep_ms: :integer,
    max_bytes: :integer,
    with_corpus: :boolean,
    corpus_cli: :string,
    user_agent: :string,
    dry_run: :boolean,
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
      Mix.Task.run("app.start")
      config = Config.from_cli(opts)

      if opts[:dry_run] do
        Mix.shell().info(inspect(config, pretty: true))
      else
        case Crawler.run(config) do
          {:ok, summary} ->
            Mix.shell().info("crawl finished: #{inspect(summary)}")

          {:error, reason} ->
            Mix.raise("crawler failed: #{inspect(reason)}")
        end
      end
    end
  end

  defp print_help do
    Mix.shell().info("""
    Usage:
      mix crawler.run [options]

    Options:
      --query <query>               Repeatable GitHub code search query
      --output <path>               NDJSON output path
      --token <token>               GitHub API token (or use GITHUB_TOKEN)
      --max-pages <n>               Max pages per query (default: 2)
      --per-page <n>                Results per page (default: 25)
      --concurrency <n>             Concurrent item workers (default: 8)
      --parser-concurrency <n>      Concurrent parser workers (default: 8)
      --request-timeout-ms <n>      HTTP request timeout in ms (default: 15000)
      --parse-timeout-ms <n>        Parse stage timeout in ms (default: 20000)
      --sleep-ms <n>                Delay between pages in ms (default: 250)
      --max-bytes <n>               Max schema file size in bytes (default: 500000)
      --with-corpus                 Run protocol-squisher corpus-analyze per file
      --corpus-cli <path|name>      protocol-squisher executable (default: protocol-squisher)
      --dry-run                     Print resolved config and exit
      --help                        Show this message
    """)
  end
end
