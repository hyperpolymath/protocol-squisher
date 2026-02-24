defmodule ProtocolSquisher.Explorer.Config do
  @moduledoc """
  Runtime configuration for the OTP crawler.
  """

  @type t :: %__MODULE__{
          github_token: String.t() | nil,
          output_path: String.t(),
          database_path: String.t(),
          queries: [String.t()],
          max_pages: pos_integer(),
          per_page: pos_integer(),
          concurrency: pos_integer(),
          parser_concurrency: pos_integer(),
          request_timeout_ms: pos_integer(),
          parse_timeout_ms: pos_integer(),
          sleep_ms: non_neg_integer(),
          max_bytes: pos_integer(),
          with_corpus: boolean(),
          corpus_cli: String.t(),
          user_agent: String.t()
        }

  @default_queries [
    "extension:proto \"syntax =\"",
    "extension:thrift \"struct\"",
    "extension:avsc \"record\"",
    "extension:capnp \"struct\"",
    "extension:fbs \"table\"",
    "extension:bop \"message\"",
    "extension:res \"type\"",
    "extension:json \"$schema\""
  ]

  defstruct [
    :github_token,
    :output_path,
    :database_path,
    :queries,
    :max_pages,
    :per_page,
    :concurrency,
    :parser_concurrency,
    :request_timeout_ms,
    :parse_timeout_ms,
    :sleep_ms,
    :max_bytes,
    :with_corpus,
    :corpus_cli,
    :user_agent
  ]

  @spec from_cli(keyword()) :: t()
  def from_cli(opts) do
    queries =
      case Keyword.get_values(opts, :query) do
        [] -> @default_queries
        values -> values
      end

    %__MODULE__{
      github_token: Keyword.get(opts, :token) || System.get_env("GITHUB_TOKEN"),
      output_path:
        Keyword.get(opts, :output) ||
          Path.expand("../../target/explorer/schemas.ndjson", File.cwd!()),
      database_path:
        Keyword.get(opts, :database_path) ||
          Path.expand("../../target/explorer/database", File.cwd!()),
      queries: queries,
      max_pages: positive_integer(Keyword.get(opts, :max_pages, 2), 2),
      per_page: positive_integer(Keyword.get(opts, :per_page, 25), 25),
      concurrency: positive_integer(Keyword.get(opts, :concurrency, 8), 8),
      parser_concurrency: positive_integer(Keyword.get(opts, :parser_concurrency, 8), 8),
      request_timeout_ms:
        positive_integer(Keyword.get(opts, :request_timeout_ms, 15_000), 15_000),
      parse_timeout_ms: positive_integer(Keyword.get(opts, :parse_timeout_ms, 20_000), 20_000),
      sleep_ms: non_negative_integer(Keyword.get(opts, :sleep_ms, 250), 250),
      max_bytes: positive_integer(Keyword.get(opts, :max_bytes, 500_000), 500_000),
      with_corpus: Keyword.get(opts, :with_corpus, false),
      corpus_cli: Keyword.get(opts, :corpus_cli, "protocol-squisher"),
      user_agent:
        Keyword.get(
          opts,
          :user_agent,
          "protocol-squisher-explorer/0.1 (+https://github.com/hyperpolymath/protocol-squisher)"
        )
    }
  end

  defp positive_integer(value, _fallback) when is_integer(value) and value > 0, do: value
  defp positive_integer(_value, fallback), do: fallback

  defp non_negative_integer(value, _fallback) when is_integer(value) and value >= 0, do: value
  defp non_negative_integer(_value, fallback), do: fallback
end
