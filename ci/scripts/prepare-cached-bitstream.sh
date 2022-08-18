#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script currently assumes it is used for chip_earlgrey_cw310.

set -e

. util/build_consts.sh

TOPLEVEL=top_earlgrey
TARGET=cw310

TOPLEVEL_BIN_DIR="$BIN_DIR/hw/$TOPLEVEL"
mkdir -p ${TOPLEVEL_BIN_DIR}

BOOTROM_SUFFIX=.scr.39.vmem
BOOTROM_VMEM_FNAME="test_rom_fpga_$TARGET$BOOTROM_SUFFIX"
BOOTROM_VMEM="$BIN_DIR/sw/device/lib/testing/test_rom/$BOOTROM_VMEM_FNAME"
test -f "$BOOTROM_VMEM" || {
  echo >&2 "No such file: $BOOTROM_VMEM"
  exit 1
}

OTP_VMEM_FNAME="otp_img_fpga_$TARGET.vmem"
OTP_VMEM="$BIN_DIR/sw/device/otp_img/$OTP_VMEM_FNAME"
test -f "$OTP_VMEM" || {
  echo >&2 "No such file: $OTP_VMEM"
  exit 1
}

bitstream_file=$(ci/scripts/target-location.sh @bitstreams//:bitstream_test_rom)
otp_mmi_file=$(ci/scripts/target-location.sh @bitstreams//:otp_mmi)
rom_mmi_file=$(ci/scripts/target-location.sh @bitstreams//:rom_mmi)

# Copy over the cached bitstream and MMI files to BIN_DIR for splicing.
cp "${bitstream_file}" "${TOPLEVEL_BIN_DIR}/lowrisc_systems_chip_earlgrey_cw310_0.1.bit"
cp "${otp_mmi_file}" "${rom_mmi_file}" "${TOPLEVEL_BIN_DIR}/"

# Splice in the test ROM. Note that OTP splicing is not handled for now.
util/fpga/splice_rom.sh -t cw310 -T earlgrey -b DV

# Remove extraneous copies.
rm "${TOPLEVEL_BIN_DIR}/lowrisc_systems_chip_earlgrey_cw310_0.1.bit.splice"
rm "${TOPLEVEL_BIN_DIR}/lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig"
