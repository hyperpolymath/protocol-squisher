defmodule ProtocolSquisher.Explorer.EmpiricalDbTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.EmpiricalDb

  test "ingests observations and persists summary" do
    database_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-empirical-db-#{System.unique_integer([:positive])}"
      )

    on_exit(fn -> File.rm_rf(database_path) end)

    {:ok, db} = EmpiricalDb.start_link(database_path: database_path)

    first_record = %{
      "format" => "protobuf",
      "repository" => "acme/alpha",
      "path" => "schemas/alpha.proto",
      "parse_error" => nil,
      "corpus_error" => nil,
      "parse_summary" => %{"entity_count" => 4},
      "corpus_analysis" => %{"transport_classes" => ["grpc", "http2"]}
    }

    second_record = %{
      "format" => "thrift",
      "repository" => "acme/beta",
      "path" => "schemas/beta.thrift",
      "parse_error" => "parse failed",
      "corpus_error" => "corpus timeout",
      "parse_summary" => %{},
      "corpus_analysis" => %{"transport_classes" => ["http2"]}
    }

    assert :ok = EmpiricalDb.ingest(db, first_record)
    assert :ok = EmpiricalDb.ingest(db, second_record)

    stats = EmpiricalDb.stats(db)

    assert stats.total_records == 2
    assert stats.parse_errors == 1
    assert stats.corpus_errors == 1
    assert stats.average_entity_count == 2.0
    assert stats.format_counts == %{"protobuf" => 1, "thrift" => 1}
    assert stats.transport_class_counts == %{"grpc" => 1, "http2" => 2}
    assert stats.repository_counts == %{"acme/alpha" => 1, "acme/beta" => 1}

    observations_path = stats.observations_path
    summary_path = stats.summary_path

    :ok = EmpiricalDb.close(db)

    observations =
      observations_path
      |> File.read!()
      |> String.split("\n", trim: true)
      |> Enum.map(&:json.decode/1)

    assert length(observations) == 2
    assert Enum.at(observations, 0)["repository"] == "acme/alpha"
    assert Enum.at(observations, 1)["repository"] == "acme/beta"

    summary = summary_path |> File.read!() |> :json.decode()

    assert summary["total_records"] == 2
    assert summary["parse_errors"] == 1
    assert summary["corpus_errors"] == 1
    assert summary["format_counts"] == %{"protobuf" => 1, "thrift" => 1}
    assert is_binary(summary["generated_at_utc"])
  end
end
