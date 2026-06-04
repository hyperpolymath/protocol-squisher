# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule ProtocolSquisher.ExplorerTest do
  use ExUnit.Case, async: true

  test "module is loadable" do
    assert {:module, ProtocolSquisher.Explorer} = Code.ensure_loaded(ProtocolSquisher.Explorer)
    assert function_exported?(ProtocolSquisher.Explorer, :run, 1)
  end
end
