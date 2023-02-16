#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage() {
    echo >&2 "ERROR: $1"
    echo >&2 ""
    echo >&2 "Usage: build-bitstream-vivado.sh <toplevel> <target>"
    echo >&2 ""
    echo >&2 "  toplevel should be something like 'top_earlgrey'."
    echo >&2 "  target should be something like 'cw310' or 'cw305'"
    exit 1
}

if [ $# != 2 ]; then
    usage "Unexpected number of arguments"
fi

TOPLEVEL=$1
TARGET=$2

case x"$TOPLEVEL" in
    xtop_earlgrey)
        HAS_SCRAMBLED_ROM=1
        HAS_OTP=1
        RUN_TOPGEN_FUSESOC=0
        ;;
    xtop_englishbreakfast)
        HAS_SCRAMBLED_ROM=0
        HAS_OTP=0
        RUN_TOPGEN_FUSESOC=1
        ;;
    *)
        usage "Unknown toplevel: $TOPLEVEL"
        ;;
esac

# Convert "top_earlgrey" to just the tea flavour: "earlgrey"
FLAVOUR=${TOPLEVEL:4}

case x"$TARGET" in
    xcw310)
        ROM_TARGET=cw310
        ;;
    xcw305)
        ROM_TARGET=cw305
        ;;
    *)
        usage "Unknown target: $TARGET"
        ;;
esac

. util/build_consts.sh

TOPLEVEL_BIN_DIR="$BIN_DIR/hw/$TOPLEVEL"

mkdir -p "$OBJ_DIR/hw"
mkdir -p "$TOPLEVEL_BIN_DIR"

if [ $HAS_SCRAMBLED_ROM == 1 ]; then
    BOOTROM_SUFFIX=.scr.39.vmem
else
    BOOTROM_SUFFIX=.32.vmem
fi

BOOTROM_VMEM_FNAME="test_rom_fpga_$ROM_TARGET$BOOTROM_SUFFIX"
BOOTROM_VMEM="$BIN_DIR/sw/device/lib/testing/test_rom/$BOOTROM_VMEM_FNAME"
test -f "$BOOTROM_VMEM" || {
    echo >&2 "No such file: $BOOTROM_VMEM"
    exit 1
}

if [ $HAS_OTP == 1 ]; then
    OTP_VMEM_FNAME="otp_img_fpga_$TARGET.vmem"
    OTP_VMEM="$BIN_DIR/sw/device/otp_img/$OTP_VMEM_FNAME"
    test -f "$OTP_VMEM" || {
        echo >&2 "No such file: $OTP_VMEM"
        exit 1
    }

    OTP_ARG=--OtpCtrlMemInitFile="$OTP_VMEM"
else
    OTP_ARG=""
fi

if [ $RUN_TOPGEN_FUSESOC == 1 ]; then
    util/topgen-fusesoc.py --files-root=. --topname="$TOPLEVEL"
    FILESET=topgen
else
    FILESET=top
fi

CORE_NAME="lowrisc:systems:chip_${FLAVOUR}_${TARGET}"

fusesoc --verbose --cores-root=. \
  run --flag=fileset_$FILESET --target=synth --setup --build \
  --build-root="$OBJ_DIR/hw" \
  "$CORE_NAME" \
  --BootRomInitFile="$BOOTROM_VMEM" \
  $OTP_ARG

BITSTREAM_FNAME="lowrisc_systems_chip_${FLAVOUR}_${TARGET}_0.1.bit"
BITSTREAM_PATH="$OBJ_DIR/hw/synth-vivado/$BITSTREAM_FNAME"
cp "$BITSTREAM_PATH" "$TOPLEVEL_BIN_DIR"

cp "$OBJ_DIR/hw/synth-vivado/rom.mmi" "$TOPLEVEL_BIN_DIR"
if [ $HAS_OTP == 1 ]; then
    cp "$OBJ_DIR/hw/synth-vivado/otp.mmi" "$TOPLEVEL_BIN_DIR"
fi
