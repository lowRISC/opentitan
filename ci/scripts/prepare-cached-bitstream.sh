#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script currently assumes it is used for chip_earlgrey_cw310.

set -ex

. util/build_consts.sh

readonly TOPLEVEL=top_earlgrey
readonly TOPLEVEL_BIN_DIR="${BIN_DIR}/hw/${TOPLEVEL}"
readonly TARGETS=(
  //hw/bitstream:test_rom
  //hw/bitstream:rom
  //hw/bitstream:rom_otp_dev
  //hw/bitstream:rom_mmi
  //hw/bitstream:otp_mmi
)
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
