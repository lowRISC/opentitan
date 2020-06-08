#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

. util/build_consts.sh

readonly VERILATED_SYSTEM_DEFAULT="build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator"
readonly SW_BUILD_DEFAULT="$DEV_BIN_DIR"

VERILATED_SYSTEM_PATH="${VERILATED_SYSTEM_PATH:-$VERILATED_SYSTEM_DEFAULT}"
SW_BUILD_PATH="${SW_BUILD_PATH:-$SW_BUILD_DEFAULT}"

BOOT_ROM_TARGET="boot_rom/boot_rom_sim_verilator.elf"

TEST_TARGETS=(
  "examples/hello_usbdev/hello_usbdev_sim_verilator.elf"
  "tests/aes_test_sim_verilator.elf"
  "tests/dif_plic_sanitytest_sim_verilator.elf"
  "tests/flash_ctrl_test_sim_verilator.elf"
  "tests/sha256_test_sim_verilator.elf"
  "tests/rv_timer_test_sim_verilator.elf"
)

FAIL_TARGETS=()
PASS_TARGETS=()
for target in "${TEST_TARGETS[@]}"; do
  echo "Executing target ${target}"
  set +e
  set -x
  pytest -v -s test/systemtest/functional_verilator_test.py \
    --test_bin "$SW_BUILD_PATH/${target}" \
    --rom_bin  "$SW_BUILD_PATH/${BOOT_ROM_TARGET}" \
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
