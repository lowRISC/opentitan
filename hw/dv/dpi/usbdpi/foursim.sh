#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

echo "Simulation with normal pins, singleended"
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator   --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf   --meminit=flash,build-bin/sw/device/examples/hello_usbdev/hello_usbdev_sim_verilator.elf -c 695965 &
sleep 1
echo 'l01 l00' > /home/mdh/github/opentitan/gpio0-write && cat /home/mdh/github/opentitan/usb0 | tee usb-post-00.log
cp uart0.log uart-00.log

echo "Simulation with flipped pins, singleended"
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator   --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf   --meminit=flash,build-bin/sw/device/examples/hello_usbdev/hello_usbdev_sim_verilator.elf -c 695965 &
sleep 1
echo 'l01 h00' > /home/mdh/github/opentitan/gpio0-write && cat /home/mdh/github/opentitan/usb0 | tee usb-post-01.log
cp uart0.log uart-01.log

echo "Simulation with normal pins, differential"
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator   --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf   --meminit=flash,build-bin/sw/device/examples/hello_usbdev/hello_usbdev_sim_verilator.elf -c 695965 &
sleep 1
echo 'h01 l00' > /home/mdh/github/opentitan/gpio0-write && cat /home/mdh/github/opentitan/usb0 | tee usb-post-10.log
cp uart0.log uart-10.log

echo "Simulation with flipped pins, differential"
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator   --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf   --meminit=flash,build-bin/sw/device/examples/hello_usbdev/hello_usbdev_sim_verilator.elf -c 695965 &
sleep 1
echo 'h01 h00' > /home/mdh/github/opentitan/gpio0-write && cat /home/mdh/github/opentitan/usb0 | tee usb-post-11.log
cp uart0.log uart-11.log

echo "Check 01 against 00"
diff usb-post-01.log usb-post-00.log
diff uart-01.log uart-00.log

echo "Check 10 against 00"
diff usb-post-10.log usb-post-00.log
diff uart-10.log uart-00.log

echo "Check 11 against 00"
diff usb-post-11.log usb-post-00.log
diff uart-11.log uart-00.log


