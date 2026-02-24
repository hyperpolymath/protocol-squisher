defmodule ProtocolSquisher.Explorer.HttpClient do
  @moduledoc false

  @spec get_json(String.t(), [{String.t(), String.t()}], pos_integer()) ::
          {:ok, %{status: non_neg_integer(), headers: map(), body: map()}} | {:error, term()}
  def get_json(url, headers, timeout_ms) do
    with {:ok, status, response_headers, body} <- get(url, headers, timeout_ms),
         {:ok, decoded} <- decode_json(body) do
      {:ok, %{status: status, headers: response_headers, body: decoded}}
    end
  end

  @spec get(String.t(), [{String.t(), String.t()}], pos_integer()) ::
          {:ok, non_neg_integer(), map(), binary()} | {:error, term()}
  def get(url, headers, timeout_ms) do
    request_headers =
      Enum.map(headers, fn {k, v} -> {String.to_charlist(k), String.to_charlist(v)} end)

    request = {String.to_charlist(url), request_headers}
    http_opts = [timeout: timeout_ms, connect_timeout: timeout_ms]
    body_opts = [body_format: :binary]

    case :httpc.request(:get, request, http_opts, body_opts) do
      {:ok, {{_http_version, status, _reason}, response_headers, body}} ->
        {:ok, status, normalize_headers(response_headers), body}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp decode_json(body) when is_binary(body) do
    try do
      {:ok, :json.decode(body)}
    rescue
      _ -> {:error, :invalid_json}
    end
  end

  defp normalize_headers(headers) do
    headers
    |> Enum.map(fn {k, v} ->
      {k |> to_string() |> String.downcase(), to_string(v)}
    end)
    |> Map.new()
  end
end
