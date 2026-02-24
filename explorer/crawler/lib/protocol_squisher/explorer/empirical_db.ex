defmodule ProtocolSquisher.Explorer.EmpiricalDb do
  @moduledoc """
  Empirical compatibility database writer.

  Persists normalized crawl observations as NDJSON and emits an aggregate
  summary JSON file for downstream pattern extraction.
  """

  use GenServer

  @type summary_t :: %{
          total_records: non_neg_integer(),
          parse_errors: non_neg_integer(),
          corpus_errors: non_neg_integer(),
          average_entity_count: float(),
          format_counts: map(),
          transport_class_counts: map(),
          observations_path: String.t(),
          summary_path: String.t()
        }

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts) do
    GenServer.start_link(__MODULE__, opts)
  end

  @spec ingest(pid(), map()) :: :ok | {:error, term()}
  def ingest(pid, record) when is_map(record) do
    GenServer.call(pid, {:ingest, record}, :infinity)
  end

  @spec stats(pid()) :: summary_t()
  def stats(pid) do
    GenServer.call(pid, :stats)
  end

  @spec close(pid()) :: :ok
  def close(pid) do
    GenServer.stop(pid, :normal)
  end

  @impl true
  def init(opts) do
    database_path = Keyword.fetch!(opts, :database_path)
    :ok = File.mkdir_p!(database_path)

    observations_path = Path.join(database_path, "compatibility-observations.ndjson")
    summary_path = Path.join(database_path, "summary.json")
    {:ok, io_device} = File.open(observations_path, [:append, :utf8])

    {:ok,
     %{
       io_device: io_device,
       observations_path: observations_path,
       summary_path: summary_path,
       total_records: 0,
       parse_errors: 0,
       corpus_errors: 0,
       total_entity_count: 0,
       format_counts: %{},
       transport_class_counts: %{},
       repository_counts: %{}
     }}
  end

  @impl true
  def handle_call({:ingest, record}, _from, state) do
    observation = observation(record)
    encoded = IO.iodata_to_binary(:json.encode(observation))

    case IO.binwrite(state.io_device, encoded <> "\n") do
      :ok ->
        {:reply, :ok, update_state(state, observation)}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  def handle_call(:stats, _from, state) do
    {:reply, summarize(state), state}
  end

  @impl true
  def terminate(_reason, state) do
    _ = persist_summary(state)
    File.close(state.io_device)
    :ok
  end

  defp observation(record) do
    transport_classes =
      case get_in(record, ["corpus_analysis", "transport_classes"]) do
        list when is_list(list) -> Enum.map(list, &to_string/1)
        _ -> []
      end

    parse_summary = Map.get(record, "parse_summary")

    %{
      "observed_at_utc" => DateTime.utc_now() |> DateTime.to_iso8601(),
      "format" => Map.get(record, "format"),
      "repository" => Map.get(record, "repository"),
      "path" => Map.get(record, "path"),
      "parse_error" => Map.get(record, "parse_error"),
      "corpus_error" => Map.get(record, "corpus_error"),
      "entity_count" => parse_entity_count(parse_summary),
      "transport_classes" => transport_classes
    }
  end

  defp parse_entity_count(%{"entity_count" => count}) when is_integer(count), do: count
  defp parse_entity_count(_), do: 0

  defp update_state(state, observation) do
    format = Map.get(observation, "format")
    repository = Map.get(observation, "repository")
    parse_error = Map.get(observation, "parse_error")
    corpus_error = Map.get(observation, "corpus_error")
    entity_count = Map.get(observation, "entity_count", 0)
    transport_classes = Map.get(observation, "transport_classes", [])

    state
    |> Map.update!(:total_records, &(&1 + 1))
    |> Map.update!(:parse_errors, fn c -> if is_nil(parse_error), do: c, else: c + 1 end)
    |> Map.update!(:corpus_errors, fn c -> if is_nil(corpus_error), do: c, else: c + 1 end)
    |> Map.update!(:total_entity_count, &(&1 + entity_count))
    |> increment_count(:format_counts, format)
    |> increment_count(:repository_counts, repository)
    |> increment_many(:transport_class_counts, transport_classes)
  end

  defp increment_many(state, key, values) when is_list(values) do
    Enum.reduce(values, state, fn value, acc -> increment_count(acc, key, value) end)
  end

  defp increment_count(state, _key, nil), do: state

  defp increment_count(state, key, value) do
    map = Map.fetch!(state, key)
    updated = Map.update(map, to_string(value), 1, &(&1 + 1))
    Map.put(state, key, updated)
  end

  defp summarize(state) do
    average_entity_count =
      if state.total_records == 0 do
        0.0
      else
        state.total_entity_count / state.total_records
      end

    %{
      total_records: state.total_records,
      parse_errors: state.parse_errors,
      corpus_errors: state.corpus_errors,
      average_entity_count: average_entity_count,
      format_counts: state.format_counts,
      transport_class_counts: state.transport_class_counts,
      repository_counts: state.repository_counts,
      observations_path: state.observations_path,
      summary_path: state.summary_path
    }
  end

  defp persist_summary(state) do
    summary =
      summarize(state)
      |> Map.put(:generated_at_utc, DateTime.utc_now() |> DateTime.to_iso8601())

    encoded = IO.iodata_to_binary(:json.encode(summary))
    File.write(state.summary_path, encoded <> "\n")
  end
end
