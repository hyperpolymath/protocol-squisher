defmodule ProtocolSquisher.Explorer.ParallelParserTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.{Config, ParallelParser}

  test "enriches records with parse summary in parallel" do
    config = Config.from_cli([])

    records = [
      %{"format" => "protobuf", "content" => "message User { string name = 1; }"},
      %{"format" => "thrift", "content" => "struct User { 1: string name }"}
    ]

    enriched = ParallelParser.parse_and_enrich(records, config)

    assert length(enriched) == 2

    Enum.each(enriched, fn rec ->
      assert is_map(rec["parse_summary"])
      assert rec["parse_error"] == nil
      assert Map.has_key?(rec["parse_summary"], "entity_count")
    end)
  end
end
