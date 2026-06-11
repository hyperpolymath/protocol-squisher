# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule ProtocolSquisher.Explorer.ConfigTest do
  use ExUnit.Case, async: true

  alias ProtocolSquisher.Explorer.Config

  test "uses defaults when no options are provided" do
    config = Config.from_cli([])

    assert config.max_pages == 2
    assert config.per_page == 25
    assert config.concurrency == 8
    assert config.parser_concurrency == 8
    assert config.parse_timeout_ms == 20_000
    assert config.with_corpus == false
    assert is_binary(config.output_path)
    assert is_binary(config.database_path)
    assert length(config.queries) > 0
  end

  test "respects repeated query flags" do
    config =
      Config.from_cli(query: "extension:proto \"syntax =\"", query: "extension:thrift \"struct\"")

    assert config.queries == ["extension:proto \"syntax =\"", "extension:thrift \"struct\""]
  end

  test "respects database path override" do
    config = Config.from_cli(database_path: "/tmp/protocol-squisher-explorer-db")

    assert config.database_path == "/tmp/protocol-squisher-explorer-db"
  end
end
