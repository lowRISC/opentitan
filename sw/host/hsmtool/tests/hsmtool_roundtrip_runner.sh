#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Create a signature and then verify it with hsmtool.
# hsmtool_roundtrip_runner.sh <key type> <key label> <file to sign>

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

SIGNATURE="$(mktemp)"
readonly SIGNATURE

run ${HSMTOOL} \
    "$1" sign --label "$2" --output "$SIGNATURE" "$3"

run ${HSMTOOL} \
    "$1" verify --label "$2" "$SIGNATURE" "$3"
