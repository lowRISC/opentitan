#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -o errexit
set -o pipefail
set -o nounset

readonly BUILD_DIR_PREFIX="build"
readonly TARGET_VERILATOR="verilator"
readonly TARGET_FPGA="fpga"

function usage() {
  cat << USAGE
Configure Meson build targets.

Usage: $0 [-r|-f]

  -f: Remove build directories before running Meson.
  -r: Force reconfiguration of build directories.

USAGE
}

FLAGS_force=false
FLAGS_reconfigure=""
while getopts 'r?:f?' flag; do
  case "${flag}" in
    f) FLAGS_force=true;;
    r) FLAGS_reconfigure="--reconfigure";;
    ?) usage && exit 1;;
    *) usage
       error "Unexpected option ${flag}"
       ;;
  esac
done

if [[ "${FLAGS_force}" == true && -n "${FLAGS_reconfigure}" ]]; then
  usage >&2
  echo "Error: -r and -f cannont be used at the same time." >&2
  exit 1
fi

if [[ ! -n "$(command -v meson)" ]]; then
  echo "Unable to find meson. Please install meson before running this command." >&2
  exit 1
fi

if [[ ! -n "$(command -v ninja)" ]]; then
  echo "Unable to find ninja. Please install ninja before running this command." >&2
  exit 1
fi

if [[ "${FLAGS_force}" == true ]]; then
  for target_suffix in "${TARGET_VERILATOR}" "${TARGET_FPGA}"; do
    rm -rf "${BUILD_DIR_PREFIX}-${target_suffix}"
  done
fi

if [[ ! -n "${FLAGS_reconfigure}" ]] ; then
  for target_suffix in "${TARGET_VERILATOR}" "${TARGET_FPGA}"; do
    if [[ -d "${BUILD_DIR_PREFIX}-${target_suffix}" ]]; then
      usage >&2
      echo "Error: ${BUILD_DIR_PREFIX}-${target_suffix} already exists. " \
           "Remove directory, or rerun $0 with the -r option" >&2
      exit 1
    fi
  done
fi

meson ${FLAGS_reconfigure} "-Dtarget=${TARGET_VERILATOR}" --cross-file=toolchain.txt \
    --buildtype=plain "${BUILD_DIR_PREFIX}-${TARGET_VERILATOR}"

meson ${FLAGS_reconfigure} "-Dtarget=${TARGET_FPGA}" --cross-file=toolchain.txt \
    --buildtype=plain "${BUILD_DIR_PREFIX}-${TARGET_FPGA}"
