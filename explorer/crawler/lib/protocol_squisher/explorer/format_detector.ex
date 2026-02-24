defmodule ProtocolSquisher.Explorer.FormatDetector do
  @moduledoc """
  Detects Protocol Squisher format IDs from file paths.
  """

  @extension_to_format %{
    "rs" => "rust",
    "py" => "python",
    "proto" => "protobuf",
    "thrift" => "thrift",
    "avsc" => "avro",
    "avdl" => "avro",
    "capnp" => "capnproto",
    "fbs" => "flatbuffers",
    "bop" => "bebop",
    "msgpack" => "messagepack",
    "res" => "rescript",
    "resi" => "rescript",
    "json" => "json-schema"
  }

  @format_to_extension %{
    "rust" => "rs",
    "python" => "py",
    "protobuf" => "proto",
    "thrift" => "thrift",
    "avro" => "avsc",
    "capnproto" => "capnp",
    "flatbuffers" => "fbs",
    "bebop" => "bop",
    "messagepack" => "msgpack",
    "rescript" => "res",
    "json-schema" => "json"
  }

  @spec detect(String.t()) :: String.t() | nil
  def detect(path) when is_binary(path) do
    case Path.extname(path) do
      <<".", extension::binary>> -> Map.get(@extension_to_format, String.downcase(extension))
      _ -> nil
    end
  end

  @spec extension_for_format(String.t()) :: String.t() | nil
  def extension_for_format(format) when is_binary(format) do
    Map.get(@format_to_extension, format)
  end
end
