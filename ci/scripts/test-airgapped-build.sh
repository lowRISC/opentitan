#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

# Prefetch bazel airgapped dependencies.
util/prep-bazel-airgapped-build.sh -f

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
sudo ip netns exec airgapped sudo -u "$USER" \
  env \
    BAZEL_BITSTREAMS_CACHE="${PWD}/bazel-airgapped/bitstreams-cache"   \
    BAZEL_PYTHON_WHEELS_REPO="${PWD}/bazel-airgapped/ot_python_wheels" \
    BITSTREAM="--offline latest"                                       \
  "${PWD}/bazel-airgapped/bazel" build                                  \
    --distdir="${PWD}/bazel-airgapped/bazel-distdir"                   \
    --repository_cache="${PWD}/bazel-airgapped/bazel-cache"            \
    --define DISABLE_VERILATOR_BUILD=true                              \
    //sw/device/silicon_creator/rom:mask_rom

exit 0
