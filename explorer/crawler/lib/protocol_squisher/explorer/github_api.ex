defmodule ProtocolSquisher.Explorer.GitHubApi do
  @moduledoc false

  alias ProtocolSquisher.Explorer.{Config, HttpClient}

  @base_url "https://api.github.com"

  @spec search_code(Config.t(), String.t(), pos_integer()) ::
          {:ok, map()} | {:error, term()}
  def search_code(%Config{} = config, query, page) do
    url =
      "#{@base_url}/search/code?q=#{URI.encode_www_form(query)}&per_page=#{config.per_page}&page=#{page}"

    with {:ok, %{status: status, headers: headers, body: body}} <-
           HttpClient.get_json(url, request_headers(config), config.request_timeout_ms),
         :ok <- require_status(status, body) do
      {:ok,
       %{
         "items" => Map.get(body, "items", []),
         "total_count" => Map.get(body, "total_count", 0),
         "rate_limit_remaining" => Map.get(headers, "x-ratelimit-remaining", "unknown")
       }}
    end
  end

  @spec fetch_content(Config.t(), map()) :: {:ok, map()} | {:error, term()}
  def fetch_content(%Config{} = config, %{"url" => url} = item) do
    with {:ok, %{status: status, body: body}} <-
           HttpClient.get_json(url, request_headers(config), config.request_timeout_ms),
         :ok <- require_status(status, body),
         :ok <- require_size(config, item),
         {:ok, content, encoding} <- decode_content(body) do
      {:ok,
       %{
         "content" => content,
         "content_encoding" => encoding,
         "download_url" => Map.get(body, "download_url"),
         "content_sha" => Map.get(body, "sha")
       }}
    end
  end

  def fetch_content(_config, _item), do: {:error, :missing_content_url}

  defp require_status(status, _body) when status in 200..299, do: :ok

  defp require_status(status, body) do
    message = Map.get(body, "message", "unexpected GitHub API response")
    {:error, {:http_error, status, message}}
  end

  defp require_size(%Config{max_bytes: max_bytes}, %{"size" => size}) when is_integer(size) do
    if size > max_bytes, do: {:error, {:schema_too_large, size, max_bytes}}, else: :ok
  end

  defp require_size(_config, _item), do: :ok

  defp decode_content(%{"encoding" => "base64", "content" => encoded}) when is_binary(encoded) do
    encoded = String.replace(encoded, "\n", "")

    case Base.decode64(encoded) do
      {:ok, decoded} when is_binary(decoded) and decoded != "" ->
        if String.valid?(decoded) do
          {:ok, decoded, "utf8"}
        else
          {:ok, Base.encode64(decoded), "base64"}
        end

      _ ->
        {:error, :invalid_base64_content}
    end
  end

  defp decode_content(%{"content" => content}) when is_binary(content) do
    {:ok, content, "utf8"}
  end

  defp decode_content(_), do: {:error, :missing_content}

  defp request_headers(%Config{github_token: token, user_agent: user_agent}) do
    headers = [
      {"accept", "application/vnd.github+json"},
      {"x-github-api-version", "2022-11-28"},
      {"user-agent", user_agent}
    ]

    if is_binary(token) and token != "" do
      headers ++ [{"authorization", "Bearer #{token}"}]
    else
      headers
    end
  end
end
