defmodule ProtocolSquisher.Explorer.CorpusAnalyzer do
  @moduledoc false

  alias ProtocolSquisher.Explorer.{Config, FormatDetector}

  @spec analyze(Config.t(), String.t(), String.t() | nil) :: {:ok, map() | nil} | {:error, term()}
  def analyze(%Config{with_corpus: false}, _content, _format), do: {:ok, nil}
  def analyze(%Config{}, _content, nil), do: {:ok, nil}

  def analyze(%Config{} = config, content, format)
      when is_binary(content) and is_binary(format) do
    with {:ok, cli} <- find_cli(config.corpus_cli),
         {:ok, extension} <- extension_for(format),
         {:ok, tmp_path} <- write_temp_schema(content, extension),
         {:ok, output} <- run_cli(cli, tmp_path, format) do
      File.rm(tmp_path)
      decode_output(output)
    else
      {:error, reason} -> {:error, reason}
    end
  end

  defp find_cli(cli) do
    cond do
      String.contains?(cli, "/") and File.exists?(cli) -> {:ok, cli}
      executable = System.find_executable(cli) -> {:ok, executable}
      true -> {:error, {:missing_cli, cli}}
    end
  end

  defp extension_for(format) do
    case FormatDetector.extension_for_format(format) do
      nil -> {:error, {:unsupported_format, format}}
      extension -> {:ok, extension}
    end
  end

  defp write_temp_schema(content, extension) do
    tmp_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-schema-#{System.unique_integer([:positive])}.#{extension}"
      )

    case File.write(tmp_path, content) do
      :ok -> {:ok, tmp_path}
      {:error, reason} -> {:error, {:temp_write_failed, reason}}
    end
  end

  defp run_cli(cli, tmp_path, format) do
    args = ["corpus-analyze", "--input", tmp_path, "--format", format]

    try do
      port =
        Port.open({:spawn_executable, String.to_charlist(cli)}, [
          :binary,
          :exit_status,
          :stderr_to_stdout,
          args: args
        ])

      collect_port_output(port, "")
    rescue
      _ -> {:error, :corpus_exec_failed}
    end
  end

  defp collect_port_output(port, acc) do
    receive do
      {^port, {:data, data}} ->
        collect_port_output(port, acc <> data)

      {^port, {:exit_status, 0}} ->
        {:ok, acc}

      {^port, {:exit_status, _status}} ->
        {:error, {:corpus_analyze_failed, acc}}
    after
      30_000 ->
        Port.close(port)
        {:error, :corpus_exec_timeout}
    end
  end

  defp decode_output(output) do
    try do
      {:ok, :json.decode(output)}
    rescue
      _ -> {:error, :invalid_corpus_json}
    end
  end
end
