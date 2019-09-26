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

BUILD_DIR=build-fpga
TARGET_PREFIX="sw/${BUILD_DIR}/rom"
FPGA_BUILD_DIR=build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/
FPGA_BIT_NAME=lowrisc_systems_top_earlgrey_nexysvideo_0.1

make -C sw "SW_BUILD_DIR=${BUILD_DIR}" SW_DIR=boot_rom distclean all

srec_cat ${TARGET_PREFIX}.bin -binary -offset 0x0 -o ${TARGET_PREFIX}.brammem \
  -vmem -Output_Block_Size 4;

util/fpga/addr4x.py -i ${TARGET_PREFIX}.brammem -o ${TARGET_PREFIX}.mem

updatemem -force --meminfo util/fpga/bram_load.mmi \
  --data ${TARGET_PREFIX}.mem \
  --bit "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.bit"  --proc dummy \
  --out "${FPGA_BUILD_DIR}/${FPGA_BIT_NAME}.splice.bit"
