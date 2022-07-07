#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Runs the OTBN smoke test (builds software, build simulation, runs simulation
# and checks expected output)

fail() {
    echo >&2 "OTBN SMOKE FAILURE: $*"
    exit 1
}

set -o pipefail
set -e

SCRIPT_DIR="$(dirname "$(readlink -e "${BASH_SOURCE[0]}")")"
UTIL_DIR="$(readlink -e "$SCRIPT_DIR/../../../../../util")" || \
  fail "Can't find OpenTitan util dir"

source "$UTIL_DIR/build_consts.sh"

SMOKE_BIN_DIR=$BIN_DIR/otbn/smoke_test
SMOKE_SRC_DIR=$REPO_TOP/hw/ip/otbn/dv/smoke

mkdir -p $SMOKE_BIN_DIR

OTBN_UTIL=$REPO_TOP/hw/ip/otbn/util

$OTBN_UTIL/otbn_as.py -o $SMOKE_BIN_DIR/smoke_test.o $SMOKE_SRC_DIR/smoke_test.s || \
    fail "Failed to assemble smoke_test.s"
$OTBN_UTIL/otbn_ld.py -o $SMOKE_BIN_DIR/smoke.elf $SMOKE_BIN_DIR/smoke_test.o || \
    fail "Failed to link smoke_test.o"

(cd $REPO_TOP;
 fusesoc --cores-root=. run --target=sim --setup --build \
         lowrisc:ip:otbn_top_sim || fail "HW Sim build failed")

RUN_LOG=`mktemp`
readonly RUN_LOG
# shellcheck disable=SC2064 # The RUN_LOG tempfile path should not change
trap "rm -rf $RUN_LOG" EXIT

timeout 5s \
  $REPO_TOP/build/lowrisc_ip_otbn_top_sim_0.1/sim-verilator/Votbn_top_sim \
  --load-elf=$SMOKE_BIN_DIR/smoke.elf -t | tee $RUN_LOG

if [ $? -eq 124 ]; then
  fail "Simulation timeout"
fi

if [ $? -ne 0 ]; then
  fail "Simulator run failed"
fi

had_diff=0
grep -A 74 "Call Stack:" $RUN_LOG | diff -U3 $SMOKE_SRC_DIR/smoke_expected.txt - || had_diff=1

if [ $had_diff == 0 ]; then
  echo "OTBN SMOKE PASS"
else
  fail "Simulator output does not match expected output"
fi
