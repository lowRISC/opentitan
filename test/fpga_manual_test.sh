#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

readonly TEST_TARGETS=("flash_ctrl"
  "hmac"
  "rv_timer"
)

echo "Compiling ROM"
make -C sw SW_DIR=boot_rom clean all

echo "Building FPGA"
. /tools/Xilinx/Vivado/2018.3/settings64.sh
fusesoc --cores-root . build lowrisc:systems:top_earlgrey_nexysvideo

echo "FPGA Error Checking"

echo "Program FPGA"
fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo:0.1

echo "Build spiflash tool"
make -C sw/host/spiflash clean all

for target in "${TEST_TARGETS[@]}"; do
    echo "Building ${target} binaries"
    make -C sw SW_DIR=tests/${target} SW_BUILD_DIR=${target}_out clean all
done

# Eventually this step should be replaced by PyTest
# How the test results will be looked at manually
# To observe results: use
# miniterm.py /dev/ttyUSBx 230400
# To find out which ttyUSB to use exactly, unplug/plug UART cable and find
# the last entry in dmesg
for target in "${TEST_TARGETS[@]}"; do
    echo "Flashing ${target}_out/sw.bin onto FPGA for tests"
    ./sw/host/spiflash/spiflash --input=sw/${target}_out/sw.bin
    sleep 5
done
