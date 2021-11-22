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
TIMELIMIT=$((15*60))

for arg in "$@"; do
  case $arg in
    --tool=*)
      OPENTITANTOOL="${arg#*=}"
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
    --verilator-flash=*)
      VERILATOR_FLASH="${arg#*=}"
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

RUST_BACKTRACE=1 ${OPENTITANTOOL} \
    --rcfile= \
    --logging=info \
    --interface=verilator \
    --verilator-bin="${VERILATOR_DIR}/sim-verilator/Vchip_sim_tb" \
    --verilator-rom="${VERILATOR_ROM}" \
    --verilator-flash="${VERILATOR_FLASH}" \
    --verilator-otp="${VERILATOR_OTP}" \
    console \
        --uart=0 \
        --exit-failure="${FAIL}" \
        --exit-success="${PASS}" \
        --timeout="${TIMELIMIT}"
