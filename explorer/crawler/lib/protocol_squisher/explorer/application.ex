# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule ProtocolSquisher.Explorer.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {Task.Supervisor, name: ProtocolSquisher.Explorer.TaskSupervisor}
    ]

    opts = [strategy: :one_for_one, name: ProtocolSquisher.Explorer.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
