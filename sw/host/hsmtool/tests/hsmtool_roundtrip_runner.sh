#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

SIGNATURE="$(mktemp)"
readonly SIGNATURE

run ${HSMTOOL} --module "$HSMTOOL_MODULE" \
    slh-dsa sign --label fake --output "$SIGNATURE" "$1"

run ${HSMTOOL} --module "$HSMTOOL_MODULE" \
    slh-dsa verify --label fake "$SIGNATURE" "$1"
