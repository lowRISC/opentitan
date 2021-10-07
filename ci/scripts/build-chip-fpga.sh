#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Build a chip-level verilator simulation
#
# Expects three arguments: the toplevel to build, the fusesoc core and
# the intermediate Verilated binary name
set -e

usage() {
  cat << USAGE
Utility script to build FPGA bitstreams.

Usage: $0 [--top TARGET_TOP] [--fpga TARGET_FPGA]

  --top: Target top: earlgrey, englishbreakfast
  --fpga: Target fpga board: cw310, cw205, nexysvideo

USAGE
}

FLAGS_TOP="earlgrey"
FLAGS_FPGA="cw310"
FLAGS_RUN_TOPGEN=false

long="fpga:,run-topgen-fusesoc,top:"
ARGS="$(getopt -o "" -l "$long" -- "$@")" || usage

eval set -- "${ARGS}"
while :
do
    case "$1" in
        --fpga)                FLAGS_FPGA="$2";       shift 2 ;;
        --run-topgen-fusesoc)  FLAGS_RUN_TOPGEN=true; shift   ;;
        --top)                 FLAGS_TOP="$2";        shift 2 ;;
        --) shift; break ;;
        *)  error "getopt / case statement mismatch"
    esac
done


# Check that there aren't any positional arguments
test $# = 0 || error "Unexpected positional arguments"

CI_DIR="$(dirname "$(readlink -e "${BASH_SOURCE}")")"
REPO_TOP="$(readlink -e "${CI_DIR}/../..")"

cd "${REPO_TOP}"

. util/build_consts.sh

mkdir -p "${OBJ_DIR}/hw"
mkdir -p "${BIN_DIR}/hw/top_${FLAGS_TOP}"

if [[ "${FLAGS_FPGA}" == "nexysvideo" ]]; then
    hw/top_earlgrey/util/top_earlgrey_reduce.py
fi

if [[ "${FLAGS_RUN_TOPGEN}" == true ]]; then
    util/topgen-fusesoc.py --files-root=. --topname="top_${FLAGS_TOP}"
fi


BOOTROM_VMEM=""
OTP_VMEM_PARAM=""
if [[ "${FLAGS_TOP}" != "englishbreakfast" ]]; then
    BOOTROM_VMEM="${BIN_DIR}/sw/device/boot_rom/boot_rom_fpga_${FLAGS_FPGA}.scr.39.vmem"
    test -f "${BOOTROM_VMEM}"
    OTP_VMEM="${BIN_DIR}/sw/device/otp_img/otp_img_fpga_${FLAGS_FPGA}.vmem"
    test -f "${OTP_VMEM}"
    OTP_VMEM_PARAM="--OtpCtrlMemInitFile=${OTP_VMEM}"
else
    BOOTROM_VMEM="${BIN_DIR}/sw/device/boot_rom/boot_rom_fpga_${FLAGS_FPGA}.32.vmem"
fi

fusesoc --cores-root=. \
    run --flag=fileset_top --target=synth --setup --build \
    --build-root="${OBJ_DIR}/hw" \
    "lowrisc:systems:chip_${FLAGS_TOP}_${FLAGS_FPGA}" \
    --BootRomInitFile="${BOOTROM_VMEM}" ${OTP_VMEM_PARAM}


cp "${OBJ_DIR}/hw/synth-vivado/lowrisc_systems_chip_${FLAGS_TOP}_${FLAGS_FPGA}_0.1.bit" \
   "${BIN_DIR}/hw/top_${FLAGS_TOP}"
