#!/bin/bash
# Run all protocol analyzers and display results

cd "$(dirname "$0")/../compiler" || exit 1

echo "=== Protocol Analyzer Suite ==="
echo "Running all 7 analyzers..."
echo ""

analyzers=(
    "bebop-simple.eph|Bebop"
    "flatbuffers-simple.eph|FlatBuffers"
    "messagepack-simple.eph|MessagePack"
    "avro-simple.eph|Avro"
    "capnproto-simple.eph|Cap'n Proto"
    "thrift-simple.eph|Thrift"
    "protobuf-simple.eph|Protocol Buffers"
)

for analyzer in "${analyzers[@]}"; do
    IFS='|' read -r file name <<< "$analyzer"
    printf "%-20s: " "$name"
    result=$(cargo run --release --quiet -- "../analyzers/$file" 2>&1 | tail -1)
    printf "%3s (overhead score)\n" "$result"
done

echo ""
echo "Lower scores = more efficient (zero-copy or minimal overhead)"
echo "Higher scores = more overhead (serialization required)"
