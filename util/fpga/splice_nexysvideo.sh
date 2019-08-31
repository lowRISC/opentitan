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


PROGRAM=boot_rom

cd sw/boot_rom
make clean ; make
srec_cat ${PROGRAM}.bin -binary -offset 0x0 -o ${PROGRAM}.brammem \
  -vmem -Output_Block_Size 4;
../../util/fpga/addr4x.py -i ${PROGRAM}.brammem -o ${PROGRAM}.mem
updatemem -force --meminfo ../../util/fpga/bram_load.mmi --data ${PROGRAM}.mem \
  --bit ../../build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/\
lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit  --proc dummy \
  --out ../../build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/\
lowrisc_systems_top_earlgrey_nexysvideo_0.1.splice.bit
