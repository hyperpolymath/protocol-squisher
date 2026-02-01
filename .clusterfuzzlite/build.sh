#!/bin/bash -eu
# SPDX-License-Identifier: PMPL-1.0-or-later

cd $SRC/vext

# Build fuzz targets with cargo-fuzz
cargo +nightly fuzz build --release

# Copy fuzz targets to output
for target in $(cargo +nightly fuzz list); do
    cp fuzz/target/x86_64-unknown-linux-gnu/release/$target $OUT/
done
