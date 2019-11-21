#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

function usage() {
    cat << USAGE
Usage: ./test/fpga_manual_test.sh -u <UART PORT ATTACHED> -n -p.
-n Controls whether a new fpga bitfile is built
-p Controls whether the existing bitfile at build/lowrisc_systems_top_earlgrey_nexysvideo_0.1
is programmed.

The following command builds the fpga, programs it onto the device and begins testing
./test/fpga_manual_test.sh -u /dev/ttyUSB0 -n -p

The following command assumes there exists a bitfile already, programs it and begins testing
./test/fpga_manual_test.sh -u /dev/ttyUSB0 -p

The following command assumes the bitfile is already programmed and begins testing
./test/fpga_manual_test.sh -u /dev/ttyUSB0

USAGE
}

FPGA_UART=
BUILD_FPGA=0
PROGRAM_FPGA=0
while getopts ':pnu:' opt; do
  case "${opt}" in
    u) FPGA_UART=$OPTARG;;
    n) BUILD_FPGA=1;;
    p) PROGRAM_FPGA=1;;
    ?) usage && exit 1;;
    *) usage
       error "Unexpected option ${opt}"
       ;;
  esac
done

# Double check a device has been specified
if [ -z "$FPGA_UART" ] ; then
  echo "Please make sure to pass FPGA's UART port as an argument to the script."
  echo "To find out which ttyUSB to use exactly, unplug/plug UART cable and find the last entry in dmesg"
  echo "Use -h for more usage details"
  exit 1;
fi


readonly TEST_TARGETS=("flash_ctrl/flash_test.bin"
  "hmac/sha256_test.bin"
  "rv_timer/rv_timer_test.bin"
)

BUILD_TARGET=${PWD}/build-fpga
./meson_init.sh

if [ ${BUILD_FPGA} -eq 1 ] ; then
  echo "Compiling ROM - this is needed in order for the build step below to correctly infer ROM"
  ninja -C ${BUILD_TARGET} sw/device/boot_rom/boot_rom.vmem

  echo "Building FPGA."
  fusesoc --cores-root . build lowrisc:systems:top_earlgrey_nexysvideo \
  --ROM_INIT_FILE=${BUILD_TARGET}/sw/device/boot_rom/boot_rom.vmem
fi

if [ ${PROGRAM_FPGA} -eq 1 ] ; then
  echo "Splice latest boot ROM and program FPGA."
  util/fpga/splice_nexysvideo.sh
  fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo
fi

echo "Build spiflash tool."
ninja -C ${BUILD_TARGET} sw/host/spiflash/spiflash

for target in "${TEST_TARGETS[@]}"; do
    echo "Building ${target} binaries."

    ninja -C ${BUILD_TARGET} sw/device/tests/${target}/
done

FAIL_TARGETS=()

# Invoke self contained tests

set +e
for target in "${TEST_TARGETS[@]}"; do
    echo "Flashing binaries onto FPGA for tests."
    pytest -s -v test/systemtest/functional_fpga_test.py \
      --test_bin ${BUILD_TARGET}/sw/device/tests/"${target}" \
      --fpga_uart ${FPGA_UART} \
      --spiflash sw/host/spiflash/spiflash

    if [[ $? == 1 ]]; then
      FAIL_TARGETS=("${FAIL_TARGETS[@]}" "${target}")
    fi

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
