#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

REPO_TOP="$(git rev-parse --show-toplevel)"
AIRGAP_DIR="${REPO_TOP}/bazel-airgapped"

mkdir -p "$AIRGAP_DIR"

# Download Bazel itself.
if [ ! -x "${AIRGAP_DIR}/bazel" ]; then
  BAZEL_VERSION="$(cat "${REPO_TOP}/.bazelversion")"
  curl --silent --location --fail \
    "https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/bazel-${BAZEL_VERSION}-linux-x86_64" \
    --output "${AIRGAP_DIR}/bazel"
  chmod +x "${AIRGAP_DIR}/bazel"
fi

# Download all Bazel repositories to a cache.
bazel vendor //... \
  --vendor_dir "${AIRGAP_DIR}/vendor-dir" \
  --repository_cache "${AIRGAP_DIR}/repository-cache"

# Copy latest bitstream from the bitstream cache.
BITSTREAM_CACHE="${HOME}/.cache/opentitan-bitstreams"
LATEST_BITSTREAM_HASH="$(cat "${BITSTREAM_CACHE}/latest.txt")"

mkdir -p "${AIRGAP_DIR}/bitstreams-cache/cache"
cp -r "${BITSTREAM_CACHE}/latest.txt" \
  "${AIRGAP_DIR}/bitstreams-cache/"
cp -r "${BITSTREAM_CACHE}/cache/${LATEST_BITSTREAM_HASH}" \
  "${AIRGAP_DIR}/bitstreams-cache/cache/"
