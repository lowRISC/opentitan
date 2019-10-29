#!/bin/bash

echo "Setting up RISC-V toolchain."
readonly DEFAULT_RISCV_TOOLS=/tools/riscv
readonly DEFAULT_RISCV_TOOLS_VERSION=latest
readonly DEFAULT_TOOLCHAIN_REQUEST_UPDATE=false

TOOLCHAIN_PATH="${TOOLCHAIN_PATH:-$DEFAULT_RISCV_TOOLS}"
TOOLCHAIN_VERSION="${TOOLCHAIN_VERSION:-$DEFAULT_RISCV_TOOLS_VERSION}"
REQUEST_UPDATE="${REQUEST_UPDATE:-$DEFAULT_TOOLCHAIN_REQUEST_UPDATE}"

if [[ ! -d "${TOOLCHAIN_PATH}/bin" ]]; then
  echo "Unable to find toolchain at: ${TOOLCHAIN_PATH}."
  REQUEST_UPDATE=true
fi

if [[ "${REQUEST_UPDATE}" = true ]]; then
  echo "Syncing toolchain directory to TOOLCHAIN_VERSION=${TOOLCHAIN_VERSION}"
  util/get-toolchain.py \
    --target-dir="${TOOLCHAIN_PATH}" \
    --release-version="${TOOLCHAIN_VERSION}" \
    --update \
    --force
fi
