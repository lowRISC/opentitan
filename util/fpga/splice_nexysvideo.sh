#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# Utility script to load MEM contents into BRAM FPGA bitfile
# Usage:
#   cd $REPO_TOP
#   ./util/fpga/splice_nexysvideo.sh

# Updated bitfile located : at the same place as raw vivado bitfile @
# $REPO_TOP/build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/
#  lowrisc_systems_top_earlgrey_nexysvideo_0.1.splice.bit
set -e

. util/build_consts.sh

TARGET_PREFIX="sw/device/boot_rom/boot_rom_fpga_nexysvideo"
TARGET="${BIN_DIR}/${TARGET_PREFIX}"
FPGA_BUILD_DIR=build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/
FPGA_BIT_NAME=lowrisc_systems_top_earlgrey_nexysvideo_0.1

./meson_init.sh
ninja -C "$BIN_DIR" "${TARGET_PREFIX}.bin"

srec_cat "${TARGET}.bin" -binary -offset 0x0 -o "${TARGET}.brammem" \
  -vmem -Output_Block_Size 4;

util/fpga/addr4x.py -i "${TARGET}.brammem" -o "${TARGET}.mem"

updatemem -force --meminfo util/fpga/bram_load.mmi \
  --data "${TARGET}.mem" \
  --bit "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit"  --proc dummy \
  --out "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit"

mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit.orig
mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit
