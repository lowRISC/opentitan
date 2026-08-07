#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

readonly HSMTOOL="sw/host/hsmtool/hsmtool"
readonly TOKEN_ARGS=("--token=fake_keys" "-u" "user" "-p" "123456" "slh-dsa")
readonly LABEL_ARGS=("--label" "fake")

SIGNATURE="$(mktemp)"
readonly SIGNATURE

set -x

"$HSMTOOL" --module="$HSMTOOL_MODULE" "${TOKEN_ARGS[@]}" \
    sign "${LABEL_ARGS[@]}" --output "$SIGNATURE" "$1"

"$HSMTOOL" --module="$HSMTOOL_MODULE" "${TOKEN_ARGS[@]}" \
    verify "${LABEL_ARGS[@]}" "$SIGNATURE" "$1"
