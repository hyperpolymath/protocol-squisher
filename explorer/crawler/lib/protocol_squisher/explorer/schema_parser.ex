defmodule ProtocolSquisher.Explorer.SchemaParser do
  @moduledoc """
  Heuristic schema parser used by the continuous-learning crawler.

  This parser intentionally avoids format-specific dependencies; it extracts
  structural hints fast enough to run in parallel across many files.
  """

  @type parse_summary :: map()

  @spec parse(String.t(), String.t()) :: {:ok, parse_summary()} | {:error, term()}
  def parse(content, format) when is_binary(content) and is_binary(format) do
    common = %{
      "kind" => "heuristic",
      "format" => format,
      "line_count" => line_count(content),
      "byte_count" => byte_size(content),
      "content_sha256" => sha256(content)
    }

    case format do
      "json-schema" -> parse_json_schema(content, common)
      _ -> parse_text_schema(content, format, common)
    end
  end

  def parse(_content, _format), do: {:error, :invalid_input}

  defp parse_json_schema(content, common) do
    try do
      decoded = :json.decode(content)

      properties =
        case decoded do
          %{"properties" => props} when is_map(props) -> map_size(props)
          _ -> 0
        end

      defs =
        case decoded do
          %{"$defs" => defs_map} when is_map(defs_map) -> map_size(defs_map)
          %{"definitions" => defs_map} when is_map(defs_map) -> map_size(defs_map)
          _ -> 0
        end

      {:ok,
       Map.merge(common, %{
         "entity_count" => properties + defs,
         "entities" => [],
         "metrics" => %{
           "property_count" => properties,
           "definition_count" => defs
         }
       })}
    rescue
      _ -> {:error, :invalid_json_schema}
    end
  end

  defp parse_text_schema(content, format, common) do
    entity_regex =
      case format do
        "protobuf" -> ~r/\b(message|enum)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "thrift" -> ~r/\b(struct|enum|service|union)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "avro" -> ~r/"name"\s*:\s*"([A-Za-z_][A-Za-z0-9_]*)"/
        "capnproto" -> ~r/\b(struct|interface|enum)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "flatbuffers" -> ~r/\b(table|struct|enum|union)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "bebop" -> ~r/\b(struct|message|enum|union)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "rescript" -> ~r/\btype\s+([A-Za-z_][A-Za-z0-9_]*)/
        "rust" -> ~r/\b(struct|enum)\s+([A-Za-z_][A-Za-z0-9_]*)/
        "python" -> ~r/\bclass\s+([A-Za-z_][A-Za-z0-9_]*)/
        "messagepack" -> ~r/\b(type|struct|class|enum)\s+([A-Za-z_][A-Za-z0-9_]*)/
        _ -> nil
      end

    entities =
      if entity_regex do
        Regex.scan(entity_regex, content)
        |> Enum.map(&extract_entity/1)
        |> Enum.reject(&is_nil/1)
        |> Enum.uniq()
        |> Enum.take(200)
      else
        []
      end

    {:ok,
     Map.merge(common, %{
       "entity_count" => length(entities),
       "entities" => entities,
       "metrics" => %{
         "token_count" => token_count(content)
       }
     })}
  end

  defp extract_entity([_whole, _kind, name]), do: name
  defp extract_entity([_whole, name]), do: name
  defp extract_entity(_), do: nil

  defp line_count(content) do
    content
    |> String.split("\n")
    |> length()
  end

  defp token_count(content) do
    content
    |> String.split(~r/\s+/, trim: true)
    |> length()
  end

  defp sha256(content) do
    :crypto.hash(:sha256, content)
    |> Base.encode16(case: :lower)
  end
end
