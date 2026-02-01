# SPDX-License-Identifier: PMPL-1.0-or-later
FROM gcr.io/oss-fuzz-base/base-builder-rust

# Copy vext source
COPY . $SRC/vext
WORKDIR $SRC/vext

# Build script will be executed by ClusterFuzzLite
COPY .clusterfuzzlite/build.sh $SRC/
