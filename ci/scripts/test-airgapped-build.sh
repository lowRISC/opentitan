#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

# Prepare the airgapped environment if it doesn't already exist.
if [ ! -d bazel-airgapped ]; then
  echo "Airgapped environment not found, preparing..." >&2
  util/prep-bazel-airgapped-build.sh
fi

# Remove the airgapped network namespace on exit.
remove_airgapped_netns() {
  # shellcheck disable=SC2317 # only reachable on EXIT.
  sudo ip netns delete airgapped
}
trap remove_airgapped_netns EXIT

# Set up a network namespace named "airgapped" with access to loopback.
sudo ip netns add airgapped
sudo ip netns exec airgapped ip addr add 127.0.0.1/8 dev lo
sudo ip netns exec airgapped ip link set dev lo up

# Enter the network namespace and perform a build.
sudo ip netns exec airgapped sudo -u "$USER" \
  env \
    BAZEL_BITSTREAMS_CACHE="${PWD}/bazel-airgapped/bitstreams-cache" \
    OT_AIRGAPPED="true"                                              \
    BITSTREAM="--offline latest"                                     \
  "${PWD}/bazel-airgapped/bazel" build                               \
    --vendor_dir "${PWD}/bazel-airgapped/bazel-vendor"               \
    --define DISABLE_VERILATOR_BUILD=true                            \
    //sw/device/silicon_creator/rom:mask_rom

exit 0
