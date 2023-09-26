#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Test that the analysis phase completes when the bitstream cache is missing
# entries.

set -e

empty_cache_dir=$(mktemp -d)
mkdir -p "${empty_cache_dir}/cache/0123456789"

echo '{"schema_version":2,"designs":{}}' \
    > "${empty_cache_dir}/cache/0123456789/manifest.json"

BAZEL_BITSTREAMS_CACHE="${empty_cache_dir}" BITSTREAM="--offline 0123456789" \
    ci/bazelisk.sh build --nobuild //...
