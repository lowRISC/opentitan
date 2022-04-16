#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The code for the quick-bazel job in azure-pipelines.yml.

# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request

set -e -x

GCP_BAZEL_CACHE_KEY=$1

mkdir -p bazel-results

# Install bazel
# TODO: this can be deleted once #12210 is merged
./bazelisk.sh

# Call bazel in all subsequent commands using bazelisk
BAZEL=./bazelisk.sh

# This queries for things that depend on //hw:verilator to exclude them
$BAZEL query \
    'rdeps(//..., //hw:verilator)' \
    | sed -e 's/^/-/' \
    > bazel-results/slow_tests.txt

run_tests() {
    local args=(
        --keep_going
        --nobuild_tests_only
        --test_tag_filters=-broken,-cw310,-verilator,-dv
        --remote_cache=https://storage.googleapis.com/opentitan-bazel-cache
        --remote_timeout=600
    )

    if [[ -n "$GCP_BAZEL_CACHE_KEY" && -f $GCP_BAZEL_CACHE_KEY ]]; then
        echo Applying GCP cache key
        args+=(--google_credentials=$GCP_BAZEL_CACHE_KEY)
    else
        # No key, download from cache only
        echo No key/invalid path to key. Download from cache only.
        args+=(--remote_upload_local_results=false)
    fi
    
    cat bazel-results/slow_tests.txt \
        | xargs \
            $BAZEL test \
            "${args[@]}" \
            -- //...
}

build_cw310_targets() {
    local args=(
        --keep_going
        --build_tag_filters=cw310
        --remote_cache=https://storage.googleapis.com/opentitan-bazel-cache
        --remote_timeout=600
    )

    if [[ -n "$GCP_BAZEL_CACHE_KEY" && -f $GCP_BAZEL_CACHE_KEY ]]; then
        echo Applying GCP cache key
        args+=(--google_credentials=$GCP_BAZEL_CACHE_KEY)
    else
        # No key, download from cache only
        echo No key/invalid path to key. Download from cache only.
        args+=(--remote_upload_local_results=false)
    fi

    $BAZEL build \
        "${args[@]}" \
        //...
}

run_tests
build_cw310_targets

