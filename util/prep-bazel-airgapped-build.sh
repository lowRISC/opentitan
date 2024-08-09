#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

if [ $# -eq 0 ]; then
  echo "USAGE: ${0} <output directory>" >&2
  exit 1
fi

REPO_TOP="$(git rev-parse --show-toplevel)"
OUT_DIR="$(realpath "$1")"

mkdir -p "$OUT_DIR"

# Download Bazel itself.
if [ ! -x "${OUT_DIR}/bazel"]; then
  BAZEL_VERSION="$(cat "${REPO_TOP}/.bazelversion")"
  curl --silent --location --fail \
    "https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/bazel-${BAZEL_VERSION}-linux-x86_64" \
    --output "${OUT_DIR}/bazel"
  chmod +x "${OUT_DIR}/bazel"
fi

bazel_targets=(
  "//..."
  "@crates_index//..."
)

# Download all Bazel repositories to a cache.
bazel fetch --repository_cache="${OUT_DIR}/repository-cache" //...
# NOTE: this line can be removed once we no longer use `WORKSPACE.bzlmod`.
bazel sync --repository_cache="${OUT_DIR}/repository-cache"

# Copy latest bitstream from the bitstream cache.
BITSTREAM_CACHE="${HOME}/.cache/opentitan-bitstreams"
LATEST_BITSTREAM_HASH="$(cat "${BITSTREAM_CACHE}/latest.txt")"

mkdir -p "${OUT_DIR}/bitstreams-cache/cache"
cp -r "${BITSTREAM_CACHE}/latest.txt" \
  "${OUT_DIR}/bitstreams-cache/"
cp -r "${BITSTREAM_CACHE}/cache/${LATEST_BITSTREAM_HASH}" \
  "${OUT_DIR}/bitstreams-cache/cache/"
