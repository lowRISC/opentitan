#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for executing opentitantool as the test harness for
# functional tests.
#
# Currently this script expects only to execute tests via verilator.

set -e

PASS="PASS"
FAIL="FAIL"
TIMELIMIT=$((60*60))

readonly OPENTITANTOOL="sw/host/opentitantool/opentitantool"
readonly CONFIG="sw/host/opentitantool/config"

for arg in "$@"; do
  case $arg in
    --interface=*)
      INTERFACE="${arg#*=}"
      shift
      ;;
    --verilator-dir=*)
      VERILATOR_DIR="${arg#*=}"
      shift
      ;;
    --verilator-rom=*)
      VERILATOR_ROM="${arg#*=}"
      shift
      ;;
    --verilator-otp=*)
      VERILATOR_OTP="${arg#*=}"
      shift
      ;;
    --pass=*)
      PASS="${arg#*=}"
      shift
      ;;
    --fail=*)
      FAIL="${arg#*=}"
      shift
      ;;
    --test-bin=*)
      TEST_BIN="${arg#*=}"
      shift
      ;;
    --timeout=*)
      TIMELIMIT="${arg#*=}"
      shift
      ;;
    *)
      echo "Unknown argument: $arg"
      exit 1
      ;;
esac
done

case ${INTERFACE} in
  verilator)
    RUST_BACKTRACE=1 ${OPENTITANTOOL} \
        --rcfile= \
        --logging=info \
        --interface=verilator \
        --conf="${CONFIG}/opentitan_verilator.json" \
        --verilator-bin="${VERILATOR_DIR}/sim-verilator/Vchip_sim_tb" \
        --verilator-rom="${VERILATOR_ROM}" \
        --verilator-flash="${TEST_BIN}" \
        --verilator-otp="${VERILATOR_OTP}" \
        console \
            --exit-failure="${FAIL}" \
            --exit-success="${PASS}" \
            --timeout="${TIMELIMIT}"
    ;;
  cw310)
    RUST_BACKTRACE=1 ${OPENTITANTOOL} \
        --rcfile= \
        --logging=info \
        --interface=cw310 \
        --conf="${CONFIG}/opentitan_cw310.json" \
        --exec="console -q -t 0" \
        --exec="bootstrap ${TEST_BIN}" \
        console \
            --exit-failure="${FAIL}" \
            --exit-success="${PASS}" \
            --timeout="${TIMELIMIT}"
    ;;
  *)
    echo "Unknown interface: ${INTERFACE}"
    exit 1
    ;;
esac
