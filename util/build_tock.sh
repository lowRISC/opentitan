#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# build_tock.sh is a wrapper to invoke Cargo from Meson. This is a workaround
# solution to read the rust-toolchain file from the Tock repository and set the
# RUSTFLAGS environment variable.

TARGET="${1}"
MODE="${2}"
MANIFEST_PATH="${3}"
TARGET_DIR="${4}"
TOOLCHAIN_FILE="${5}"
export MESON_SOURCE_ROOT="${6}"
export MESON_BUILD_ROOT="${7}"
export RUSTFLAGS="${8}"

if [[ "${MODE}" == "release" ]]; then
	RELEASE_FLAG="--release"
fi

cargo +"$(cat ${TOOLCHAIN_FILE})" build \
	--target "${TARGET}" \
	--manifest-path "${MANIFEST_PATH}" \
	--target-dir "${TARGET_DIR}" \
	--features="${TOCK_FEATURES}" \
	${RELEASE_FLAG}
