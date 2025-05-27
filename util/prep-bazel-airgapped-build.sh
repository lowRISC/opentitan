#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script prepares a directory that can be used inside an airgapped
# environment to build any Bazel target in this project without a network
# connection.
#
# This includes the correct Bazel binary, all external dependencies, and the
# latest valid bitstream.

set -euo pipefail

# These variables can be overridden by the caller.

: "${REPO_TOP:=$(git rev-parse --show-toplevel)}"

: "${BAZEL_AIRGAPPED_DIR:=${REPO_TOP}/bazel-airgapped}"
: "${BAZEL_BITSTREAM_DIR:=${BAZEL_AIRGAPPED_DIR}/bitstreams-cache}"
: "${BAZEL_VENDOR_DIR:=${BAZEL_AIRGAPPED_DIR}/bazel-vendor}"

: "${BAZEL:=${BAZEL_AIRGAPPED_DIR}/bazel}"
: "${BAZEL_VERSION:=$(cat "${REPO_TOP}/.bazelversion")}"

: "${SYSTEM_BITSTREAM_CACHE:=${HOME}/.cache/opentitan-bitstreams}"

if [ -d "$BAZEL_AIRGAPPED_DIR" ]; then
  if [ "${1-}" == "-f" ]; then
    rm -rf "$BAZEL_AIRGAPPED_DIR"
  else
    echo "ERROR: ${BAZEL_AIRGAPPED_DIR} already exists." >&2
    echo "       Use -f to delete and recreate it."     >&2
    exit 1
  fi
fi

# Create directories
mkdir -p "$BAZEL_AIRGAPPED_DIR"
mkdir -p "$BAZEL_BITSTREAM_DIR"
mkdir -p "$BAZEL_VENDOR_DIR"

echo "Downloading Bazel binary..."

curl --silent --location \
  "https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/bazel-${BAZEL_VERSION}-linux-x86_64" \
  --output "${BAZEL_AIRGAPPED_DIR}/bazel"

chmod +x "$BAZEL"

echo
echo "Vendoring external Bazel dependencies..."

# Ask Bazel to download all external dependencies needed to build all targets on
# the current host platform into a directory.
"$BAZEL" vendor --vendor_dir "$BAZEL_VENDOR_DIR" //...

echo
echo "Copying latest bitstreams..."

# We don't need all bitstreams in the cache, we just need the latest one so
# that the cache is "initialized" and "offline" mode will work correctly.
# The revision named in latest.txt is not necessarily on disk. Induce the
# cache backend to fetch the latest bitstreams.
BITSTREAM=latest "${BAZEL}" fetch @bitstreams//...

latest_hash_file="${SYSTEM_BITSTREAM_CACHE}/latest.txt"
latest_hash="$(cat "$latest_hash_file")"

cp -r "${SYSTEM_BITSTREAM_CACHE}/cache/${latest_hash}" "${BAZEL_BITSTREAM_DIR}/cache/"
cp "$latest_hash_file" "$BAZEL_BITSTREAM_DIR"

echo
echo "Done!"

echo
echo "To perform an airgapped build, ship the contents of ${BAZEL_AIRGAPPED_DIR}"
echo "to your airgapped environment and then:"
echo
echo "${BAZEL_AIRGAPPED_DIR}/bazel build --vendor_dir ${BAZEL_VENDOR_DIR} <label>"
