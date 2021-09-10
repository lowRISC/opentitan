#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# Utility script to load ROM contents into FPGA bitstream.
# Usage:
#   cd $REPO_TOP
#   ./util/fpga/splice_rom.sh
#
# The updated bitstream is located at the same place as the original Vivado bitstream e.g. at
# $REPO_TOP/build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/
#  lowrisc_systems_chip_earlgrey_cw310_0.1.bit
#
# A copy of the original bitstream is created at e.g. at
# $REPO_TOP/build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/
#  lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig
set -e

. util/build_consts.sh

# Change these variables when using the script for a different top level and/or FPGA board.
TARGET_BOARD="cw310"
TARGET_TOP="earlgrey"
TARGET_FILE_EXT=".scr.39.vmem"

TARGET_PREFIX="sw/device/boot_rom"
TARGET_EXPORT="${TARGET_PREFIX}/boot_rom_export_fpga_${TARGET_BOARD}"
TARGET="${BIN_DIR}/${TARGET_PREFIX}/boot_rom_fpga_${TARGET_BOARD}"

FPGA_BUILD_DIR=build/lowrisc_systems_chip_${TARGET_TOP}_${TARGET_BOARD}_0.1/synth-vivado
FPGA_MMI_PATH=${FPGA_BUILD_DIR}/lowrisc_systems_chip_${TARGET_TOP}_${TARGET_BOARD}_0.1.runs/impl_1
FPGA_BIT_NAME=lowrisc_systems_chip_${TARGET_TOP}_${TARGET_BOARD}_0.1

# Create the Vivado image for splicing.
hw/ip/rom_ctrl/util/gen_vivado_mem_image.py "${TARGET}${TARGET_FILE_EXT}" "${TARGET}.updatemem.mem"

# Splice the ROM.
# The --debug flag is undocumented and causes updatemem to print out the INIT_XX
# values of the four BRAM cells. These values are also oberservable when opening
# the implemented design in Vivado and then inspecting the cell properties of
# the corresponding BRAM cells. This information is very useful when debugging
# the splicing flow.
updatemem -force --meminfo "${FPGA_BUILD_DIR}/rom.mmi" \
  --data "${TARGET}.updatemem.mem" \
  --bit "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit"  --proc dummy \
  --out "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit" \
  --debug

mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit.orig
mv ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit ${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit
