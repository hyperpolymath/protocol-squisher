defmodule ProtocolSquisher.Explorer.SchemaSinkTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.SchemaSink

  test "writes ndjson records and tracks count" do
    output_path =
      Path.join(
        System.tmp_dir!(),
        "protocol-squisher-schema-sink-#{System.unique_integer([:positive])}.ndjson"
      )

    on_exit(fn -> File.rm(output_path) end)

    {:ok, sink} = SchemaSink.start_link(output_path: output_path)

    assert :ok = SchemaSink.write(sink, %{"id" => 1, "format" => "protobuf"})
    assert :ok = SchemaSink.write(sink, %{"id" => 2, "format" => "thrift"})

    assert %{count: 2, output_path: ^output_path} = SchemaSink.stats(sink)

    :ok = SchemaSink.close(sink)

    lines = output_path |> File.read!() |> String.split("\n", trim: true)
    assert length(lines) == 2
  end
end
