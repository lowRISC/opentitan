#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The code for the quick-bazel job in azure-pipelines.yml.

# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request

set -e -x

mkdir -p bazel-results

# This queries for things that depend on //hw:verilator to exclude them
bazel query \
    'rdeps(//..., //hw:verilator)' \
    | sed -e 's/^/-/' \
    > bazel-results/slow_tests.txt

run_tests() {
    cat bazel-results/slow_tests.txt \
        | xargs \
            bazel test \
            --keep_going \
            --nobuild_tests_only \
            --test_tag_filters=-broken,-cw310,-verilator \
            -- //...
}

build_cw310_targets() {
    bazel build \
        --keep_going \
        --build_tag_filters=cw310 \
        //...
}

run_tests
build_cw310_targets

