#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

if test "$#" -ne 1; then
  echo "Usage: $0 <top name>" >&2
  echo "Example: $0 earlgrey" >&2
  exit 1
fi
readonly TOP_NAME="$1"

. util/build_consts.sh

readonly TOPLEVEL_BIN_DIR="${BIN_DIR}/hw/top_${TOP_NAME}"
readonly TARGET_PREFIX=@bitstreams//:chip_
readonly TARGET_SUFFIXES=(
  _cw310_bitstream
  _cw310_rom_mmi
  _cw310_otp_mmi
)
TARGETS=()
for suffix in "${TARGET_SUFFIXES[@]}"; do
  TARGETS+=("${TARGET_PREFIX}${TOP_NAME}${suffix}")
done
readonly TARGETS
readonly BAZEL_OPTS=(
  "--define"
  "bitstream=gcp_splice"
)

BITSTREAM=HEAD ci/bazelisk.sh build "${BAZEL_OPTS[@]}" "${TARGETS[@]}"
mkdir -p "${TOPLEVEL_BIN_DIR}"
for target in "${TARGETS[@]}"; do
  src="$(ci/scripts/target-location.sh "${target}" "${BAZEL_OPTS[@]}")"
  dst="${TOPLEVEL_BIN_DIR}/$(basename "$(ci/scripts/target-location.sh "${target}")")"
  cp -vL "${src}" "${dst}"
done
