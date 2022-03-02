#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# invoke_cargo.sh is a wrapper to invoke Cargo from Meson. This is a workaround
# solution to read the rust-toolchain file and set the the relevant environment
# variables.

CARGO="${1}"
CARGO_FLAGS="${2}"
CARGO_FMT_FLAG="${3}"
export RUSTFLAGS="${4}"

TOOLCHAIN_FILE="${5}"
if [[ -f $TOOLCHAIN_FILE ]]; then
    TOOLCHAIN="$(cat ${TOOLCHAIN_FILE})"
fi

export MESON_SOURCE_ROOT="${6}"
export MESON_BUILD_ROOT="${7}"

if [ "${CARGO_TEST}" == 1 ]; then
    echo "CARGO TEST BUILD!"
    "${CARGO}" fmt ${CARGO_FMT_FLAG}
    "${CARGO}" +"${TOOLCHAIN}" test ${CARGO_FLAGS} --workspace
    "${CARGO}" +"${TOOLCHAIN}" build ${CARGO_FLAGS}
else
    "${CARGO}" fmt ${CARGO_FMT_FLAG}
    "${CARGO}" +"${TOOLCHAIN}" build ${CARGO_FLAGS}  
fi
