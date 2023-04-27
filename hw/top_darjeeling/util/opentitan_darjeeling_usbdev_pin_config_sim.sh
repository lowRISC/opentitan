#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Simulator executable
VERILATOR=build/lowrisc_systems_chip_earlgrey_verilator_0.1/sim-verilator/Vchip_earlgrey_verilator

# Code to load
ROMCODE=build-bin/sw/device/lib/testing/test_rom/test_rom_sim_verilator.scr.39.vmem
FLASH=build-bin/sw/device/examples/hello_usbdev/hello_usbdev_sim_verilator.elf
OTP=build-bin/sw/device/otp_img/otp_img_sim_verilator.vmem

# Where simulator output or control fifos are put
VFILE_DIR=.

# How long to simulate
SIM_CYCLES=757000

# Expected output
EXPECT_USB=hw/top_earlgrey/util/opentitan_earlgrey_usbdev_expected-usb
EXPECT_UART=hw/top_earlgrey/util/opentitan_earlgrey_usbdev_expected-uart

# Expected differences in output between expected and actual
IGNORE_EX_UART="-I Build.Date -I Version -I Built.at"
# Expected differences in output between noflip se and the others
IGNORE_USB="-I Pullup.change"
IGNORE_UART="-I PHY.settings"

echo "Simulation with normal pins, singleended"
$VERILATOR --meminit=rom,$ROMCODE --meminit=flash,$FLASH --meminit=otp,$OTP -c $SIM_CYCLES &
sleep 1
echo 'l01 l00' > $VFILE_DIR/gpio0-write && cat $VFILE_DIR/gpio0-read
cp $VFILE_DIR/usb0.log $VFILE_DIR/usb-noflip-se.log
cp $VFILE_DIR/uart0.log $VFILE_DIR/uart-noflip-se.log


echo "Simulation with flipped pins, singleended"
$VERILATOR --meminit=rom,$ROMCODE --meminit=flash,$FLASH --meminit=otp,$OTP -c $SIM_CYCLES &
sleep 1
echo 'l01 h00' > $VFILE_DIR/gpio0-write && cat $VFILE_DIR/gpio0-read
cp $VFILE_DIR/usb0.log $VFILE_DIR/usb-flip-se.log
cp $VFILE_DIR/uart0.log $VFILE_DIR/uart-flip-se.log

echo "Simulation with normal pins, differential"
$VERILATOR --meminit=rom,$ROMCODE --meminit=flash,$FLASH --meminit=otp,$OTP -c $SIM_CYCLES &
sleep 1
echo 'h01 l00' > $VFILE_DIR/gpio0-write && cat $VFILE_DIR/gpio0-read
cp $VFILE_DIR/usb0.log $VFILE_DIR/usb-noflip-diff.log
cp $VFILE_DIR/uart0.log $VFILE_DIR/uart-noflip-diff.log

echo "Simulation with flipped pins, differential"
$VERILATOR --meminit=rom,$ROMCODE --meminit=flash,$FLASH --meminit=otp,$OTP -c $SIM_CYCLES &
sleep 1
echo 'h01 h00' > $VFILE_DIR/gpio0-write && cat $VFILE_DIR/gpio0-read
cp $VFILE_DIR/usb0.log $VFILE_DIR/usb-flip-diff.log
cp $VFILE_DIR/uart0.log $VFILE_DIR/uart-flip-diff.log

echo "Check No Flip Single Ended against expected logs"
diff $VFILE_DIR/usb-noflip-se.log $EXPECT_USB
diff $IGNORE_EX_UART $VFILE_DIR/uart-noflip-se.log $EXPECT_UART

echo "Check Flipped Single Ended against No Flip Single Ended"
diff $IGNORE_USB $VFILE_DIR/usb-flip-se.log $VFILE_DIR/usb-noflip-se.log
diff $IGNORE_UART $VFILE_DIR/uart-flip-se.log $VFILE_DIR/uart-noflip-se.log

echo "Check No Flip differential against No Flip Single Ended"
diff $IGNORE_USB $VFILE_DIR/usb-noflip-diff.log $VFILE_DIR/usb-noflip-se.log
diff $IGNORE_UART $VFILE_DIR/uart-noflip-diff.log $VFILE_DIR/uart-noflip-se.log

echo "Check Flipped differential against No Flip Single Ended"
diff $IGNORE_USB $VFILE_DIR/usb-flip-diff.log $VFILE_DIR/usb-noflip-se.log
diff $IGNORE_UART $VFILE_DIR/uart-flip-diff.log $VFILE_DIR/uart-noflip-se.log
