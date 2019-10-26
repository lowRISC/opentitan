#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

readonly DEFAULT_RISCV_TOOLS=/tools/riscv
readonly DEFAULT_RISCV_TOOLS_VERSION=latest
readonly DEFAULT_TOOLCHAIN_REQUEST_UPDATE=false

TOOLCHAIN_PATH="${TOOLCHAIN_PATH:-$DEFAULT_RISCV_TOOLS}"
TOOLCHAIN_VERSION="${TOOLCHAIN_VERSION:-$DEFAULT_RISCV_TOOLS_VERSION}"
REQUEST_UPDATE="${REQUEST_UPDATE:-$DEFAULT_TOOLCHAIN_REQUEST_UPDATE}"

if [ ! -d "${TOOLCHAIN_PATH}/bin" ]; then
  echo "Unable to find toolchain at: ${TOOLCHAIN_PATH}."
  REQUEST_UPDATE=true
fi

export RV_TOOLS="${TOOLCHAIN_PATH}/bin"
echo "Setting toolchain path to RV_TOOLS=${RV_TOOLS}"

if [ "${REQUEST_UPDATE}" = true ]; then
  echo "Syncing toolchain directory to TOOLCHAIN_VERSION=${TOOLCHAIN_VERSION}"
  util/get-toolchain.py "--target-dir=${TOOLCHAIN_PATH}" --update --force \
    "--release-version=${TOOLCHAIN_VERSION}"
fi

readonly BUILD_TARGETS=("boot_rom"
  "examples/hello_usbdev"
  "examples/hello_world"
  "tests/flash_ctrl"
  "tests/hmac"
  "tests/rv_timer"
)

FAIL_TARGETS=()
PASS_TARGETS=()
for target in "${BUILD_TARGETS[@]}"; do
  echo "Building target ${target}"
  if make -C sw/device "SW_DIR=${target}" "SW_BUILD_DIR=../build/${target}"; then
    PASS_TARGETS=("${PASS_TARGETS[@]}" "${target}")
  else
    FAIL_TARGETS=("${FAIL_TARGETS[@]}" "${target}")
  fi
done

echo "* PASS_TARGETS"
for target in "${PASS_TARGETS[@]}"; do
  echo "${target}"
done

if [ ${#FAIL_TARGETS[@]} -eq 0 ]; then
  echo "BUILD PASS!"
else
  echo "* FAIL_TARGETS"
  for target in "${FAIL_TARGETS[@]}"; do
    echo "${target}"
  done
  echo "BUILD FAILED!"
  exit 1
fi
