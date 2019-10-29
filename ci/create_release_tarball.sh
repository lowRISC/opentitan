#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

if [ $# -lt 1 ]; then
    echo "Usage: $0 OUT_DIR"
    exit 1
fi

OUT_DIR=$(readlink -f $1)

STAGING_BASE_DIR=$(mktemp -d)
VERSION=$(git describe --always)
STAGING_DIR=$STAGING_BASE_DIR/opentitan-$VERSION

mkdir -p $STAGING_DIR

# Collect hardware release files
mkdir -p $STAGING_DIR/hw
cp build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit $STAGING_DIR/hw
#cp build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator $STAGING_DIR/hw

# Collect software
mkdir -p $STAGING_DIR/sw

# device software
mkdir -p $STAGING_DIR/sw/device

function copy_sw {
    mkdir -p $2
    cp $1/*.elf $2
    cp $1/*.vmem $2
    cp $1/*.bin $2
}

copy_sw sw/build/boot_rom $STAGING_DIR/sw/device/boot_rom
copy_sw sw/build/examples/hello_world $STAGING_DIR/sw/device/examples/hello_world
for t in flash_ctrl hmac rv_timer; do
    copy_sw sw/build/tests/$t $STAGING_DIR/sw/device/tests/$t
done

# host software
mkdir -p $STAGING_DIR/sw/host
cp sw/host/spiflash/spiflash $STAGING_DIR/sw/host


(cd $STAGING_BASE_DIR; tar -cJf $OUT_DIR/opentitan-$VERSION.tar.xz opentitan-$VERSION)

echo $OUT_DIR/opentitan-$VERSION.tar.xz
