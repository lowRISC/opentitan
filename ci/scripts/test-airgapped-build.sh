#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

# Prefetch bazel airgapped dependencies if not already done.
if [ ! -d bazel-airgapped ]; then
  echo "Airgapped environment not found, preparing..." >&2
  util/prep-bazel-airgapped-build.sh -f
fi

# Clean out bazel cache so no remnants exist for test.
"${PWD}/bazel-airgapped/bazel" clean --expunge

# Use unshare to create an ephemeral, unprivileged user and network namespace.
# --map-root-user allows us to bring up the loopback interface without host CAP_NET_ADMIN capabilities.
unshare --user --net --map-root-user bash -c '
  # Set up access to loopback.
  ip addr add 127.0.0.1/8 dev lo
  ip link set dev lo up

  # Perform the airgapped builds.
  env \
    BAZEL_BITSTREAMS_CACHE="${PWD}/bazel-airgapped/bitstreams-cache" \
    OT_AIRGAPPED="true"                                              \
    BITSTREAM="--offline latest"                                     \
  "${PWD}/bazel-airgapped/bazel" build                               \
    --distdir="${PWD}/bazel-airgapped/bazel-distdir"                 \
    --vendor_dir="${PWD}/bazel-airgapped/bazel-vendor"               \
    --define DISABLE_VERILATOR_BUILD=true                            \
    //sw/device/silicon_creator/rom:mask_rom
'

exit 0
