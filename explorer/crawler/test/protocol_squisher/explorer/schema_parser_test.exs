defmodule ProtocolSquisher.Explorer.SchemaParserTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.SchemaParser

  test "parses protobuf entities heuristically" do
    content = """
    syntax = \"proto3\";
    message User { string name = 1; }
    enum Status { ACTIVE = 0; }
    """

    assert {:ok, summary} = SchemaParser.parse(content, "protobuf")
    assert summary["format"] == "protobuf"
    assert summary["entity_count"] >= 2
    assert "User" in summary["entities"]
    assert "Status" in summary["entities"]
    assert summary["metrics"]["token_count"] > 0
  end

  test "parses json-schema metrics" do
    content = """
    {
      "$schema": "https://json-schema.org/draft/2020-12/schema",
      "type": "object",
      "properties": {
        "name": {"type": "string"},
        "age": {"type": "integer"}
      },
      "$defs": {
        "Address": {"type": "object"}
      }
    }
    """

    assert {:ok, summary} = SchemaParser.parse(content, "json-schema")
    assert summary["metrics"]["property_count"] == 2
    assert summary["metrics"]["definition_count"] == 1
    assert summary["entity_count"] == 3
  end
end
