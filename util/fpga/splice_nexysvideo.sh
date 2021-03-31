#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# Utility script to load MEM contents into BRAM FPGA bitfile
# Usage:
#   cd $REPO_TOP
#   ./util/fpga/splice_nexysvideo.sh

# Updated bitfile located at the same place as raw vivado bitfile at
# $REPO_TOP/build/lowrisc_systems_chip_earlgrey_nexysvideo_0.1/synth-vivado/
#  lowrisc_systems_chip_earlgrey_nexysvideo_0.1.bit
# A copy of the original bitfile is created at
# $REPO_TOP/build/lowrisc_systems_chip_earlgrey_nexysvideo_0.1/synth-vivado/
#  lowrisc_systems_chip_earlgrey_nexysvideo_0.1.bit.orig
set -e

. util/build_consts.sh

TARGET_PREFIX="sw/device/boot_rom/"
TARGET_EXPORT="${TARGET_PREFIX}/boot_rom_export_fpga_nexysvideo"
TARGET="${BIN_DIR}/${TARGET_PREFIX}/boot_rom_fpga_nexysvideo"

FPGA_BUILD_DIR=build/lowrisc_systems_chip_earlgrey_nexysvideo_0.1/synth-vivado/
FPGA_BIT_NAME=lowrisc_systems_chip_earlgrey_nexysvideo_0.1

./meson_init.sh
ninja -C "${OBJ_DIR}" "${TARGET_EXPORT}"

srec_cat "${TARGET}.bin" -binary -offset 0x0 -o "${TARGET}.brammem" \
  -vmem -Output_Block_Size 4;

util/fpga/addr4x.py -i "${TARGET}.brammem" -o "${TARGET}.mem"

# The --debug flag is undocumented and causes updatemem to print out the INIT_XX
# values of the four BRAM cells. These values are also oberservable when opening
# the implemented design in Vivado and then inspecting the cell properties of
# the corresponding BRAM cells. This information is very useful when debugging
# the splicing flow.
updatemem -force --meminfo util/fpga/bram_load.mmi \
  --data "${TARGET}.mem" \
  --bit "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit"  --proc dummy \
  --out "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit" \
  --debug

mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit.orig
mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit
