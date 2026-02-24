defmodule ProtocolSquisher.Explorer.ParallelParser do
  @moduledoc false

  alias ProtocolSquisher.Explorer.{Config, CorpusAnalyzer, SchemaParser}

  @spec parse_and_enrich([map()], Config.t()) :: [map()]
  def parse_and_enrich(records, %Config{} = config) do
    stream_opts = [
      max_concurrency: config.parser_concurrency,
      timeout: config.parse_timeout_ms,
      on_timeout: :kill_task,
      ordered: false,
      supervisor: ProtocolSquisher.Explorer.TaskSupervisor
    ]

    Task.async_stream(records, &enrich_record(&1, config), stream_opts)
    |> Enum.map(fn
      {:ok, record} -> record
      {:exit, reason} -> %{"record_error" => inspect(reason)}
    end)
  end

  defp enrich_record(%{"content" => content, "format" => format} = record, %Config{} = config)
       when is_binary(content) and is_binary(format) do
    {parse_summary, parse_error} = parse_result(SchemaParser.parse(content, format))

    {corpus_analysis, corpus_error} =
      corpus_result(CorpusAnalyzer.analyze(config, content, format))

    record
    |> Map.put("parse_summary", parse_summary)
    |> Map.put("parse_error", parse_error)
    |> Map.put("corpus_analysis", corpus_analysis)
    |> Map.put("corpus_error", corpus_error)
  end

  defp enrich_record(record, _config) do
    record
    |> Map.put_new("parse_summary", nil)
    |> Map.put_new("parse_error", "invalid_record")
    |> Map.put_new("corpus_analysis", nil)
    |> Map.put_new("corpus_error", "invalid_record")
  end

  defp parse_result({:ok, summary}), do: {summary, nil}
  defp parse_result({:error, reason}), do: {nil, inspect(reason)}

  defp corpus_result({:ok, summary}), do: {summary, nil}
  defp corpus_result({:error, reason}), do: {nil, inspect(reason)}
end
