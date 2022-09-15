#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script currently assumes it is used for chip_earlgrey_cw310.

set -ex

. util/build_consts.sh

TOPLEVEL=top_earlgrey
TOPLEVEL_BIN_DIR="${BIN_DIR}/hw/${TOPLEVEL}"

BITSTREAM=HEAD ci/bazelisk.sh build --define bitstream=gcp_splice \
  //hw/bitstream:test_rom \
  //hw/bitstream:rom \
  //hw/bitstream:rom_otp_dev \
  //hw/bitstream:rom_mmi \
  //hw/bitstream:otp_mmi

mkdir -p ${TOPLEVEL_BIN_DIR}
cp -rLvt "${TOPLEVEL_BIN_DIR}" \
  "$(ci/scripts/target-location.sh //hw/bitstream:test_rom)" \
  "$(ci/scripts/target-location.sh //hw/bitstream:rom)" \
  "$(ci/scripts/target-location.sh //hw/bitstream:rom_otp_dev)"\
  "$(ci/scripts/target-location.sh //hw/bitstream:rom_mmi)" \
  "$(ci/scripts/target-location.sh //hw/bitstream:otp_mmi)"
