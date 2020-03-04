#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# build_tock.sh is a wrapper to invoke Cargo from Meson. This is a workaround
# solution to read the rust-toolchain file from the Tock repository and set the
# RUSTFLAGS environment variable.

TARGET="${1}"
MANIFEST_PATH="${2}"
TARGET_DIR="${3}"
TOOLCHAIN_FILE="${4}"
export RUSTFLAGS="${5}"

cargo +"$(cat ${TOOLCHAIN_FILE})" build \
	--target "${TARGET}" \
	--manifest-path "${MANIFEST_PATH}" \
	--target-dir "${TARGET_DIR}"
