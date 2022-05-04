#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

ci/bazelisk.sh test \
    --build_tests_only=true \
    --test_timeout=900,900,2400,-1 \
    --local_test_jobs=4 \
    --local_cpu_resources=4 \
    --test_timeout_filters=long \
    --test_tag_filters=verilator,-failing_verilator,-broken \
    --test_output=errors \
    //sw/device/...
