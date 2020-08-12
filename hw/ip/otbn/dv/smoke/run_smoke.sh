#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Runs the OTBN smoke test (builds software, build simulation, runs simulation
# and checks expected output)

fail() {
    echo >&2 "OTBN SMOKE FAILURE: $@"
    exit 1
}

set -o pipefail

SCRIPT_DIR="$(dirname "$(readlink -e "$BASH_SOURCE")")"
UTIL_DIR="$(readlink -e "$SCRIPT_DIR/../../../../../util")" || \
  fail "Can't find OpenTitan util dir"

source "$UTIL_DIR/build_consts.sh"

SMOKE_BIN_DIR=$BIN_DIR/otbn/smoke_test
SMOKE_SRC_DIR=$REPO_TOP/hw/ip/otbn/dv/smoke

mkdir -p $SMOKE_BIN_DIR

$REPO_TOP/hw/ip/otbn/util/build.sh $SMOKE_SRC_DIR/smoke_test.S \
  $SMOKE_BIN_DIR/smoke || fail "Software build failed"

pushd $REPO_TOP

fusesoc --cores-root=. run --target=sim --setup --build \
  lowrisc:ip:otbn_top_sim || fail "HW Sim build failed"

popd

RUN_LOG=`mktemp`
trap "rm -rf $RUN_LOG" EXIT

timeout 5s \
  $REPO_TOP/build/lowrisc_ip_otbn_top_sim_0.1/sim-verilator/Votbn_top_sim \
  --meminit=imem,$SMOKE_BIN_DIR/smoke_imem.elf \
  --meminit=dmem,$SMOKE_BIN_DIR/smoke_dmem.elf | tee $RUN_LOG

if [ $? -eq 124 ]; then
  fail "Simulation timeout"
fi

if [ $? -ne 0 ]; then
  fail "Simulator run failed"
fi

grep -A 33 "Final Register Values:" $RUN_LOG | diff $SMOKE_SRC_DIR/smoke_expected.txt -

if [ $? -eq 0 ]; then
  echo "OTBN SMOKE PASS"
else
  fail "Simulator output does not match expected output"
fi
