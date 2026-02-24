defmodule ProtocolSquisher.Explorer.PatternExtractorTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.PatternExtractor

  test "extracts synthesis hints from summary json" do
    database_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-pattern-extractor-#{System.unique_integer([:positive])}"
      )

    summary_path = Path.join(database_path, "summary.json")
    output_path = Path.join(database_path, "synthesis-hints.json")
    File.mkdir_p!(database_path)

    on_exit(fn -> File.rm_rf(database_path) end)

    summary = %{
      "total_records" => 100,
      "parse_errors" => 12,
      "corpus_errors" => 2,
      "format_counts" => %{"protobuf" => 60, "thrift" => 40},
      "transport_class_counts" => %{
        "Concorde" => 10,
        "Economy" => 25,
        "Wheelbarrow" => 65
      }
    }

    encoded = IO.iodata_to_binary(:json.encode(summary))
    File.write!(summary_path, encoded <> "\n")

    assert {:ok, hints} = PatternExtractor.extract(summary_path, output_path)

    assert hints["record_count"] == 100
    assert hints["output_path"] == output_path
    assert hints["suggestion_weights"]["WidenType"] > 1.0
    assert hints["suggestion_weights"]["MakeOptional"] > 1.0
    assert hints["transport_class_distribution"]["Wheelbarrow"] > 0.6

    notes = hints["notes"] || []
    assert Enum.any?(notes, &String.contains?(&1, "Wheelbarrow-heavy corpus detected"))
    assert Enum.any?(notes, &String.contains?(&1, "Parse error rate is high"))

    persisted = output_path |> File.read!() |> :json.decode()
    assert persisted["version"] == 1
    assert persisted["record_count"] == 100
  end
end
