defmodule ProtocolSquisher.Explorer.Crawler do
  @moduledoc """
  Crawls GitHub schema files and records normalized crawl output to NDJSON.
  """

  require Logger

  alias ProtocolSquisher.Explorer.{Config, CorpusAnalyzer, FormatDetector, GitHubApi, SchemaSink}

  @type crawl_summary :: %{
          queries: non_neg_integer(),
          pages: non_neg_integer(),
          items_seen: non_neg_integer(),
          written: non_neg_integer(),
          errors: non_neg_integer(),
          output_path: String.t()
        }

  @spec run(Config.t()) :: {:ok, crawl_summary()} | {:error, term()}
  def run(%Config{} = config) do
    Logger.info("starting GitHub schema crawl for #{length(config.queries)} query sets")

    with {:ok, sink} <- SchemaSink.start_link(output_path: config.output_path) do
      summary =
        Enum.reduce(config.queries, empty_summary(), fn query, summary ->
          crawl_query(query, 1, config, sink, %{summary | queries: summary.queries + 1})
        end)

      sink_stats = SchemaSink.stats(sink)
      :ok = SchemaSink.close(sink)

      {:ok,
       summary
       |> Map.put(:written, sink_stats.count)
       |> Map.put(:output_path, sink_stats.output_path)}
    end
  end

  defp empty_summary do
    %{queries: 0, pages: 0, items_seen: 0, written: 0, errors: 0, output_path: ""}
  end

  defp crawl_query(_query, page, %Config{max_pages: max_pages}, _sink, summary)
       when page > max_pages,
       do: summary

  defp crawl_query(query, page, %Config{} = config, sink, summary) do
    case GitHubApi.search_code(config, query, page) do
      {:ok, %{"items" => []}} ->
        summary

      {:ok, %{"items" => items}} ->
        Logger.info("query=#{inspect(query)} page=#{page} items=#{length(items)}")

        updated_summary =
          items
          |> process_items(query, config, sink)
          |> merge_counts(%{
            summary
            | pages: summary.pages + 1,
              items_seen: summary.items_seen + length(items)
          })

        Process.sleep(config.sleep_ms)
        crawl_query(query, page + 1, config, sink, updated_summary)

      {:error, reason} ->
        Logger.warning("query=#{inspect(query)} page=#{page} failed: #{inspect(reason)}")
        %{summary | errors: summary.errors + 1}
    end
  end

  defp process_items(items, query, %Config{} = config, sink) do
    stream_opts = [
      max_concurrency: config.concurrency,
      timeout: config.request_timeout_ms * 2,
      on_timeout: :kill_task,
      ordered: false,
      supervisor: ProtocolSquisher.Explorer.TaskSupervisor
    ]

    Enum.reduce(
      Task.async_stream(items, &process_item(&1, query, config), stream_opts),
      %{written: 0, errors: 0},
      fn
        {:ok, {:ok, record}}, acc ->
          case SchemaSink.write(sink, record) do
            :ok -> %{acc | written: acc.written + 1}
            {:error, _reason} -> %{acc | errors: acc.errors + 1}
          end

        {:ok, {:error, reason}}, acc ->
          Logger.debug("item skipped: #{inspect(reason)}")
          %{acc | errors: acc.errors + 1}

        {:exit, reason}, acc ->
          Logger.warning("item worker crashed: #{inspect(reason)}")
          %{acc | errors: acc.errors + 1}
      end
    )
  end

  defp process_item(item, query, %Config{} = config) do
    path = Map.get(item, "path")
    format = if is_binary(path), do: FormatDetector.detect(path), else: nil

    with true <- is_binary(path) || {:error, :missing_path},
         true <- is_binary(format) || {:error, {:unsupported_format, path}},
         {:ok, content_payload} <- GitHubApi.fetch_content(config, item) do
      {corpus_analysis, corpus_error} =
        corpus_result(CorpusAnalyzer.analyze(config, content_payload["content"], format))

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
         "download_url" => content_payload["download_url"],
         "corpus_analysis" => corpus_analysis,
         "corpus_error" => corpus_error
       }}
    else
      false -> {:error, :invalid_item}
      {:error, reason} -> {:error, reason}
    end
  end

  defp corpus_result({:ok, analysis}), do: {analysis, nil}
  defp corpus_result({:error, reason}), do: {nil, inspect(reason)}

  defp merge_counts(counts, summary) do
    %{summary | written: summary.written + counts.written, errors: summary.errors + counts.errors}
  end
end
