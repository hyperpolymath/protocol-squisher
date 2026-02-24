defmodule Mix.Tasks.Crawler.Pattern.ExtractTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "writes synthesis hints file from summary input" do
    database_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-pattern-task-#{System.unique_integer([:positive])}"
      )

    summary_path = Path.join(database_path, "summary.json")
    output_path = Path.join(database_path, "synthesis-hints.json")
    File.mkdir_p!(database_path)

    on_exit(fn -> File.rm_rf(database_path) end)

    summary = %{
      "total_records" => 10,
      "parse_errors" => 0,
      "corpus_errors" => 0,
      "format_counts" => %{"protobuf" => 7, "thrift" => 3},
      "transport_class_counts" => %{"Concorde" => 5, "Economy" => 5}
    }

    encoded = IO.iodata_to_binary(:json.encode(summary))
    File.write!(summary_path, encoded <> "\n")

    output =
      capture_io(fn ->
        Mix.Tasks.Crawler.Pattern.Extract.run([
          "--summary",
          summary_path,
          "--output",
          output_path
        ])
      end)

    assert output =~ "wrote synthesis hints"
    assert output =~ "records: 10"
    assert File.exists?(output_path)
  end
end
