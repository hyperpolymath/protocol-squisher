defmodule ProtocolSquisher.Explorer.Crawler do
  @moduledoc """
  Crawls GitHub schema files and records normalized crawl output to NDJSON.
  """

  require Logger

  alias ProtocolSquisher.Explorer.{
    Config,
    EmpiricalDb,
    FormatDetector,
    GitHubApi,
    ParallelParser,
    SchemaSink
  }

  @type crawl_summary :: %{
          queries: non_neg_integer(),
          pages: non_neg_integer(),
          items_seen: non_neg_integer(),
          written: non_neg_integer(),
          errors: non_neg_integer(),
          output_path: String.t(),
          database_path: String.t(),
          observations_path: String.t(),
          summary_path: String.t()
        }

  @spec run(Config.t()) :: {:ok, crawl_summary()} | {:error, term()}
  def run(%Config{} = config) do
    Logger.info("starting GitHub schema crawl for #{length(config.queries)} query sets")

    with {:ok, sink} <- SchemaSink.start_link(output_path: config.output_path),
         {:ok, db} <- EmpiricalDb.start_link(database_path: config.database_path) do
      summary =
        Enum.reduce(config.queries, empty_summary(), fn query, summary ->
          crawl_query(query, 1, config, sink, db, %{summary | queries: summary.queries + 1})
        end)

      sink_stats = SchemaSink.stats(sink)
      db_stats = EmpiricalDb.stats(db)
      :ok = SchemaSink.close(sink)
      :ok = EmpiricalDb.close(db)

      {:ok,
       summary
       |> Map.put(:written, sink_stats.count)
       |> Map.put(:output_path, sink_stats.output_path)
       |> Map.put(:database_path, Path.dirname(db_stats.summary_path))
       |> Map.put(:observations_path, db_stats.observations_path)
       |> Map.put(:summary_path, db_stats.summary_path)}
    end
  end

  defp empty_summary do
    %{
      queries: 0,
      pages: 0,
      items_seen: 0,
      written: 0,
      errors: 0,
      output_path: "",
      database_path: "",
      observations_path: "",
      summary_path: ""
    }
  end

  defp crawl_query(_query, page, %Config{max_pages: max_pages}, _sink, _db, summary)
       when page > max_pages,
       do: summary

  defp crawl_query(query, page, %Config{} = config, sink, db, summary) do
    case GitHubApi.search_code(config, query, page) do
      {:ok, %{"items" => []}} ->
        summary

      {:ok, %{"items" => items}} ->
        Logger.info("query=#{inspect(query)} page=#{page} items=#{length(items)}")

        updated_summary =
          items
          |> process_items(query, config, sink, db)
          |> merge_counts(%{
            summary
            | pages: summary.pages + 1,
              items_seen: summary.items_seen + length(items)
          })

        Process.sleep(config.sleep_ms)
        crawl_query(query, page + 1, config, sink, db, updated_summary)

      {:error, reason} ->
        Logger.warning("query=#{inspect(query)} page=#{page} failed: #{inspect(reason)}")
        %{summary | errors: summary.errors + 1}
    end
  end

  defp process_items(items, query, %Config{} = config, sink, db) do
    fetch_stream_opts = [
      max_concurrency: config.concurrency,
      timeout: config.request_timeout_ms * 2,
      on_timeout: :kill_task,
      ordered: false,
      supervisor: ProtocolSquisher.Explorer.TaskSupervisor
    ]

    {fetched_records, fetch_errors} =
      Enum.reduce(
        Task.async_stream(items, &fetch_item(&1, query, config), fetch_stream_opts),
        {[], 0},
        fn
          {:ok, {:ok, record}}, {records, errors} ->
            {[record | records], errors}

          {:ok, {:error, reason}}, {records, errors} ->
            Logger.debug("fetch skipped: #{inspect(reason)}")
            {records, errors + 1}

          {:exit, reason}, {records, errors} ->
            Logger.warning("fetch worker crashed: #{inspect(reason)}")
            {records, errors + 1}
        end
      )

    fetched_records
    |> ParallelParser.parse_and_enrich(config)
    |> Enum.reduce(%{written: 0, errors: fetch_errors}, fn
      %{"record_error" => reason}, acc ->
        Logger.warning("parse worker crashed: #{reason}")
        %{acc | errors: acc.errors + 1}

      record, acc ->
        with :ok <- SchemaSink.write(sink, record),
             :ok <- EmpiricalDb.ingest(db, record) do
          %{acc | written: acc.written + 1}
        else
          {:error, _reason} ->
            %{acc | errors: acc.errors + 1}
        end
    end)
  end

  defp fetch_item(item, query, %Config{} = config) do
    path = Map.get(item, "path")
    format = if is_binary(path), do: FormatDetector.detect(path), else: nil

    with true <- is_binary(path) || {:error, :missing_path},
         true <- is_binary(format) || {:error, {:unsupported_format, path}},
         {:ok, content_payload} <- GitHubApi.fetch_content(config, item) do
      {:ok,
       %{
         "fetched_at_utc" => DateTime.utc_now() |> DateTime.to_iso8601(),
         "query" => query,
         "format" => format,
         "repository" => get_in(item, ["repository", "full_name"]),
         "repository_url" => get_in(item, ["repository", "html_url"]),
         "path" => path,
         "sha" => Map.get(item, "sha"),
         "html_url" => Map.get(item, "html_url"),
         "api_url" => Map.get(item, "url"),
         "content_encoding" => content_payload["content_encoding"],
         "content" => content_payload["content"],
         "content_sha" => content_payload["content_sha"],
         "download_url" => content_payload["download_url"]
       }}
    else
      false -> {:error, :invalid_item}
      {:error, reason} -> {:error, reason}
    end
  end

  defp merge_counts(counts, summary) do
    %{summary | written: summary.written + counts.written, errors: summary.errors + counts.errors}
  end
end
