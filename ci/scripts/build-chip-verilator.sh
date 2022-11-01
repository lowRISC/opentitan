#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Build a chip-level verilator simulation
#
# Expects three arguments: the toplevel to build, the fusesoc core and
# the intermediate Verilated binary name

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: build-chip-verilator.sh <toplevel>"
    exit 1
fi
tl="$1"

case "$tl" in
    earlgrey)
        fileset=fileset_top
        fusesoc_core=lowrisc:dv:chip_verilator_sim
        vname=Vchip_sim_tb
        verilator_options="--threads 4"
        make_options="-j 4"
        ;;
    englishbreakfast)
        fileset=fileset_topgen
        fusesoc_core=lowrisc:systems:chip_englishbreakfast_verilator
        vname=Vchip_englishbreakfast_verilator
        # Englishbreakfast on CI runs on a 2-core CPU
        verilator_options="--threads 2"
        make_options="-j 2"
        util/topgen-fusesoc.py --files-root=. --topname=top_englishbreakfast
        ;;
    *)
        echo >&2 "Unknown toplevel: $tl"
        exit 1
esac

# Move to project root
cd "$(git rev-parse --show-toplevel)"

. util/build_consts.sh

set -x

mkdir -p "$OBJ_DIR/hw"
mkdir -p "$BIN_DIR/hw/top_${tl}"

fusesoc --cores-root=. \
  run --flag=$fileset --target=sim --setup --build \
  --build-root="$OBJ_DIR/hw" \
  $fusesoc_core \
  --verilator_options="${verilator_options}" \
  --make_options="${make_options}"

cp "$OBJ_DIR/hw/sim-verilator/${vname}" \
   "$BIN_DIR/hw/top_${tl}/Vchip_${tl}_verilator"
