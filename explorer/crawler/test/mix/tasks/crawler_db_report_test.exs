defmodule Mix.Tasks.Crawler.Db.ReportTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "prints a report from summary json" do
    database_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-db-report-#{System.unique_integer([:positive])}"
      )

    summary_path = Path.join(database_path, "summary.json")
    File.mkdir_p!(database_path)

    on_exit(fn -> File.rm_rf(database_path) end)

    summary = %{
      "total_records" => 3,
      "parse_errors" => 1,
      "corpus_errors" => 0,
      "average_entity_count" => 2.3333333333333335,
      "format_counts" => %{"protobuf" => 2, "thrift" => 1},
      "transport_class_counts" => %{"grpc" => 2, "http2" => 1},
      "repository_counts" => %{"acme/alpha" => 2, "acme/beta" => 1}
    }

    encoded = IO.iodata_to_binary(:json.encode(summary))
    File.write!(summary_path, encoded <> "\n")

    output =
      capture_io(fn ->
        Mix.Tasks.Crawler.Db.Report.run(["--summary", summary_path, "--top-repos", "1"])
      end)

    assert output =~ "Empirical Compatibility Database"
    assert output =~ "records: 3"
    assert output =~ "parse_errors: 1"
    assert output =~ "format_counts:"
    assert output =~ "protobuf: 2"
    assert output =~ "top_repositories:"
    assert output =~ "acme/alpha: 2"
    refute output =~ "acme/beta: 1"
  end

  test "prints help text" do
    output =
      capture_io(fn ->
        Mix.Tasks.Crawler.Db.Report.run(["--help"])
      end)

    assert output =~ "Usage:"
    assert output =~ "mix crawler.db.report [options]"
  end
end
