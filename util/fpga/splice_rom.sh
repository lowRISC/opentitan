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

function usage() {
  cat << USAGE
Utility script to load ROM contents into the FPGA bitstream.

Usage: $0 [-t TARGET_BOARD] [-T TARGET_TOP] [-b DV | PROD]

  - t: Target board: cw310, cw305.
  - T: Target top: earlgrey.
  - b: ROM binary, set to either DV or PROD.

ROM binary targets (-b):
  - DV: sw/device/lib/testing/test_rom
  - PROD: sw/device/silicon_creator/rom

USAGE
}

# Change these variables when using the script for a different top level and/or FPGA board.
FLAGS_TARGET_BOARD="cw310"
FLAGS_TARGET_TOP="earlgrey"
FLAGS_BIN="DV"

# `getopts` usage
# - The initial colon in the optstring is to suppress the default error
#   handling.
# - The remaining options are specified in alphabetical order, and the case
#   statement should match this order.
# - Only options that take an argument should have a following colon.
# - The case statement contains two additional cases:
#   - when `$flag` = `?`, this is an unexpected option.
#   - when `$flag` = `:`, this is the case that a flag which requires an
#     argument is not provided one. In both cases, `$OPTARG` contains the
#     relevant parsed option.
# - After option parsing is finished, we `shift` by `$OPTIND - 1` so that the
#   remaining (unprocessed) arguments are in `$@` (and $1, $2, $3 etc.).
while getopts ':b:t:T:' flag; do
  case "${flag}" in
    b) FLAGS_BIN="${OPTARG}";;
    t) FLAGS_TARGET_BOARD="${OPTARG}";;
    T) FLAGS_TARGET_TOP="${OPTARG}";;
    \?) echo "Unexpected option: -${OPTARG}" >&2
        usage
        exit 1
        ;;
    :) echo "Option -${OPTARG} requires an argument" >&2
       usage
       exit 1
       ;;
    *) echo "Internal Error: Unhandled option: -${flag}" >&2
       exit 1
       ;;
  esac
done
shift $((OPTIND - 1))

# We do not accept additional arguments.
if [[ "$#" -gt 0 ]]; then
  echo "Unexpected arguments:" "$@" >&2
  exit 1
fi

TARGET_PREFIX=""
if [[ ${FLAGS_BIN} == "DV" ]]; then
  TARGET_PREFIX="sw/device/lib/testing/test_rom/test_rom"
elif [[ ${FLAGS_BIN} == "PROD" ]]; then
  TARGET_PREFIX="sw/device/silicon_creator/rom/rom"
else
  echo "Invalid -b option: ${FLAGS_BIN}; expected DV or PROD." >&2
  exit 1
fi

TARGET_BOARD="${FLAGS_TARGET_BOARD}"
TARGET_TOP="${FLAGS_TARGET_TOP}"
TARGET_FILE_EXT=".scr.39.vmem"
TARGET="${BIN_DIR}/${TARGET_PREFIX}_fpga_${TARGET_BOARD}"
TARGET_PATH="${TARGET}${TARGET_FILE_EXT}"

FPGA_BIN_DIR="${BIN_DIR}/hw/top_${TARGET_TOP}"
FPGA_BIT_NAME="lowrisc_systems_chip_${TARGET_TOP}_${TARGET_BOARD}_0.1"

# Make sure all inputs are available.
if [[ ! -f "${TARGET_PATH}" ]]; then
  echo "Unable to find ROM base image ${TARGET_PATH}." >&2
  exit 1
fi

if [[ ! -f "${FPGA_BIN_DIR}/rom.mmi" ]]; then
  echo "Unable to find ${FPGA_BIN_DIR}/rom.mmi." >&2
  exit 1
fi

if [[ ! -f "${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit" ]]; then
  echo "Unable to find ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit." >&2
  exit 1
fi

# Create the Vivado image for splicing.
hw/ip/rom_ctrl/util/gen_vivado_mem_image.py \
  "${TARGET_PATH}" \
  "${TARGET}.updatemem.mem" \
  --swap-nibbles

# Splice the ROM.
# The --debug flag is undocumented and causes updatemem to print out the INIT_XX
# values of the four BRAM cells. These values are also oberservable when opening
# the implemented design in Vivado and then inspecting the cell properties of
# the corresponding BRAM cells. This information is very useful when debugging
# the splicing flow.
updatemem -force --meminfo "${FPGA_BIN_DIR}/rom.mmi" \
  --data "${TARGET}.updatemem.mem" \
  --bit "${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit"  --proc dummy \
  --out "${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.splice.bit" \
  --debug

mv ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit.orig

# Rename to the canonical bitstream output name to simplify interaction with
# other tools, and create a copy with a .splice suffix to be able to
# export the artifact in CI.
mv ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.splice.bit ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit
cp ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit ${FPGA_BIN_DIR}/${FPGA_BIT_NAME}.bit.splice
