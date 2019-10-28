#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

readonly VERILATED_SYSTEM_DEFAULT="build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator"
readonly SW_BUILD_DEFAULT="build-verilator"

VERILATED_SYSTEM_PATH="${VERILATED_SYSTEM_PATH:-$VERILATED_SYSTEM_DEFAULT}"
SW_BUILD_PATH="${SW_BUILD_PATH:-$SW_BUILD_DEFAULT}"

readonly TEST_TARGETS=("tests/flash_ctrl/flash_test.vmem"
  "tests/hmac/sha256_test.vmem"
  "tests/rv_timer/rv_timer_test.vmem"
)

FAIL_TARGETS=()
PASS_TARGETS=()
for target in "${TEST_TARGETS[@]}"; do
  echo "Executing target ${target}"
  set +e
  set -x
  pytest -s test/systemtest/functional_verilator_test.py \
    --test_bin "$SW_BUILD_PATH/sw/device/${target}" \
    --rom_bin  "$SW_BUILD_PATH/sw/device/boot_rom/boot_rom.vmem" \
    --verilator_model "$VERILATED_SYSTEM_PATH"
  if [[ $? == 0 ]]; then
    PASS_TARGETS=("${PASS_TARGETS[@]}" "${target}")
  else
    FAIL_TARGETS=("${FAIL_TARGETS[@]}" "${target}")
  fi
  set +x
  set -e
done

echo "Passing targets:"
for target in "${PASS_TARGETS[@]}"; do
  echo "* ${target}"
done

if [ ${#FAIL_TARGETS[@]} -eq 0 ]; then
  echo "TESTS PASS!"
else
  echo
  echo "Failing targets:"
  for target in "${FAIL_TARGETS[@]}"; do
    echo "* ${target}"
  done
  echo
  echo "TESTS FAILED!"
  exit 1
fi
