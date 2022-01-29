#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The code for the quick-bazel job in azure-pipelines.yml.

# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request

bazel query "rdeps(//..., //hw:verilator)" | \
            sed -e 's/^/-/' | \
            xargs bazel test --nobuild_tests_only --test_tag_filters=-cw310,-verilator -- //...

