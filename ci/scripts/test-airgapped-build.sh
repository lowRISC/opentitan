#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

if [ $# -eq 0 ]; then
  echo "USAGE: ${0} <airgap directory>" >&2
  exit 1
fi

AIRGAP_DIR="$(realpath "$1")"

# Remove the airgapped network namespace.
remove_airgapped_netns() {
  sudo ip netns delete airgapped
}
trap remove_airgapped_netns EXIT

# Set up a network namespace named "airgapped" with access to loopback.
sudo ip netns add airgapped
sudo ip netns exec airgapped ip addr add 127.0.0.1/8 dev lo
sudo ip netns exec airgapped ip link set dev lo up

# Enter the network namespace and perform several builds.
export BAZEL_BITSTREAMS_CACHE="${AIRGAP_DIR}/bitstreams-cache"
export BITSTREAM="--offline latest"

TARGET_PATTERN_FILE="$(mktemp)"
echo //sw/device/silicon_creator/rom:mask_rom > "$TARGET_PATTERN_FILE"

sudo ip netns exec airgapped sudo -u "$USER" \
  bazel-airgapped/bazel cquery \
    --repository_cache="${AIRGAP_DIR}/repository-cache" \
    --noinclude_aspects \
    --output=starlark \
    --starlark:expr='"-{}".format(target.label)' \
    --define DISABLE_VERILATOR_BUILD=true \
    -- "rdeps(//..., kind(bitstream_splice, //...))" \
    | sudo -u "$USER" tee -a "$TARGET_PATTERN_FILE"

echo Building target pattern:
cat "$TARGET_PATTERN_FILE"

sudo ip netns exec airgapped sudo -u "$USER" \
  bazel-airgapped/bazel build \
    --repository_cache="${AIRGAP_DIR}/repository-cache" \
    --define DISABLE_VERILATOR_BUILD=true \
    --target_pattern_file="$TARGET_PATTERN_FILE"
