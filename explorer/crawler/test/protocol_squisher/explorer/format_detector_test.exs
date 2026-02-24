defmodule ProtocolSquisher.Explorer.FormatDetectorTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.FormatDetector

  test "detects known formats by extension" do
    assert FormatDetector.detect("schema.proto") == "protobuf"
    assert FormatDetector.detect("types.avsc") == "avro"
    assert FormatDetector.detect("model.res") == "rescript"
    assert FormatDetector.detect("schema.json") == "json-schema"
  end

  test "returns nil for unsupported extension" do
    assert FormatDetector.detect("notes.txt") == nil
  end

  test "maps format back to canonical extension" do
    assert FormatDetector.extension_for_format("protobuf") == "proto"
    assert FormatDetector.extension_for_format("json-schema") == "json"
  end
end
