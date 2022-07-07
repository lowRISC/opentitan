#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Runs the CRC32 pre-dv testbench (build simulation,
# runs simulation and checks expected output)

fail() {
    echo >&2 "PRE-DV FAILURE: $*"
    exit 1
}

set -o pipefail

SCRIPT_DIR="$(dirname "$(readlink -e "${BASH_SOURCE[0]}")")"
UTIL_DIR="$(readlink -e "$SCRIPT_DIR/../../../../../util")" || \
  fail "Can't find OpenTitan util dir"

source "$UTIL_DIR/build_consts.sh"

PREDV_DIR=$REPO_TOP/hw/ip/prim/pre_dv/prim_crc32

(cd $REPO_TOP || exit;
 fusesoc --cores-root=. run --target=sim --setup --build \
         lowrisc:prim:crc32_sim || fail "HW Sim build failed")

RUN_LOG=`mktemp`
readonly RUN_LOG
# shellcheck disable=SC2064 # The RUN_LOG tempfile path should not change
trap "rm -rf $RUN_LOG" EXIT

timeout 5s \
  $REPO_TOP/build/lowrisc_prim_crc32_sim_0/sim-verilator/Vprim_crc32_sim | \
  tee $RUN_LOG

if [ $? -eq 124 ]; then
  fail "Simulation timeout"
fi

if [ $? -ne 0 ]; then
  fail "Simulator run failed"
fi

grep -A 97 "00000000" $RUN_LOG | diff $PREDV_DIR/predv_expected.txt -

if [ $? -eq 0 ]; then
  echo "PRE-DV PASS"
else
  fail "Simulator output does not match expected output"
fi
