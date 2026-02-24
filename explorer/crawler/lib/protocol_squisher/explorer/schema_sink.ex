defmodule ProtocolSquisher.Explorer.SchemaSink do
  @moduledoc false

  use GenServer

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts) do
    GenServer.start_link(__MODULE__, opts)
  end

  @spec write(pid(), map()) :: :ok | {:error, term()}
  def write(pid, record) when is_map(record) do
    GenServer.call(pid, {:write, record}, :infinity)
  end

  @spec stats(pid()) :: %{count: non_neg_integer(), output_path: String.t()}
  def stats(pid) do
    GenServer.call(pid, :stats)
  end

  @spec close(pid()) :: :ok
  def close(pid) do
    GenServer.stop(pid, :normal)
  end

  @impl true
  def init(opts) do
    output_path = Keyword.fetch!(opts, :output_path)
    :ok = File.mkdir_p!(Path.dirname(output_path))
    {:ok, io_device} = File.open(output_path, [:append, :utf8])

    {:ok, %{io_device: io_device, output_path: output_path, count: 0}}
  end

  @impl true
  def handle_call({:write, record}, _from, state) do
    encoded = IO.iodata_to_binary(:json.encode(record))

    case IO.binwrite(state.io_device, encoded <> "\n") do
      :ok ->
        {:reply, :ok, %{state | count: state.count + 1}}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  def handle_call(:stats, _from, state) do
    {:reply, %{count: state.count, output_path: state.output_path}, state}
  end

  @impl true
  def terminate(_reason, state) do
    File.close(state.io_device)
    :ok
  end
end
