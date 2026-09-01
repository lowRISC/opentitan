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

# `clean --expunge` leaves the repository cache intact, and it could satisfy
# fetches the vendor dir is missing. It must stay empty across the build.
EMPTY_REPO_CACHE="${PWD}/bazel-airgapped/empty-repo-cache"
rm -rf "${EMPTY_REPO_CACHE}"
mkdir -p "${EMPTY_REPO_CACHE}"

# Enter a network namespace and perform several builds. `-r` maps us to uid 0
# in a new user namespace, which avoids needing real root but means tools
# without HOME in their action env (e.g. rustfmt) resolve ~ to the unreadable
# /root, hence the tmpfs. Loopback must be up to reach the bazel server.
unshare -rnm bash -c '
    ip link set dev lo up &&
    mount -t tmpfs tmpfs /root &&
    exec "$@"' -- \
  env \
    BAZEL_BITSTREAMS_CACHE="${PWD}/bazel-airgapped/bitstreams-cache" \
    OT_AIRGAPPED="true"                                              \
    BITSTREAM="--offline latest"                                     \
   "${PWD}/bazel-airgapped/bazel"                                    \
    --nohome_rc --nosystem_rc                                        \
    build                                                            \
    --repository_cache="${EMPTY_REPO_CACHE}"                         \
    --vendor_dir="${PWD}/bazel-airgapped/bazel-vendor"               \
    --define DISABLE_VERILATOR_BUILD=true                            \
    //sw/device/silicon_creator/rom:mask_rom                         \
    //sw/device/tests:uart_smoketest_fpga_cw340_sival

if [ -n "$(ls -A "${EMPTY_REPO_CACHE}")" ]; then
  echo "ERROR: bazel populated the repository cache; deps were not all vendored" >&2
  exit 1
fi

exit 0
