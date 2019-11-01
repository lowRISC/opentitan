#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

readonly DEFAULT_RISCV_TOOLS=/tools/riscv
readonly DEFAULT_RISCV_TOOLS_VERSION=latest
readonly DEFAULT_TOOLCHAIN_REQUEST_UPDATE=false
readonly DEFAULT_DIST_DIR=dist

TOOLCHAIN_PATH="${TOOLCHAIN_PATH:-$DEFAULT_RISCV_TOOLS}"
TOOLCHAIN_VERSION="${TOOLCHAIN_VERSION:-$DEFAULT_RISCV_TOOLS_VERSION}"
REQUEST_UPDATE="${REQUEST_UPDATE:-$DEFAULT_TOOLCHAIN_REQUEST_UPDATE}"
DIST_DIR="${DIST_DIR:-$DEFAULT_DIST_DIR}"

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

readonly BUILD_VARIANTS=("sim"
  "fpga"
)

FAIL_TARGETS=()
PASS_TARGETS=()
for target in "${BUILD_TARGETS[@]}"; do
  for variant in "${BUILD_VARIANTS[@]}"; do
    echo "Building target ${target} (variant ${variant})"

    if [ "${variant}" = "sim" ]; then
      make_arg_sim="SIM=1"
    else
      make_arg_sim=""
    fi

    make -C sw/device ${make_arg_sim} "SW_DIR=${target}" \
      "SW_BUILD_DIR=../build/${variant}/${target}"
    if [ $? -eq 0 ]; then
      PASS_TARGETS=("${PASS_TARGETS[@]}" "${target}-${variant}")
    else
      FAIL_TARGETS=("${FAIL_TARGETS[@]}" "${target}-${variant}")
    fi

    target_staging_dir="${DIST_DIR}/sw/device/${variant}/${target}"
    mkdir -p "$target_staging_dir"
    cp sw/build/${variant}/${target}/*.elf "${target_staging_dir}"
    cp sw/build/${variant}/${target}/*.vmem "${target_staging_dir}"
    cp sw/build/${variant}/${target}/*.bin "${target_staging_dir}"
  done
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
