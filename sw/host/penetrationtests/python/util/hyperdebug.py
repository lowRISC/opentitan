# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import time
from subprocess import PIPE, Popen
from typing import Optional

import serial
from serial.tools.list_ports import comports


class HyperDebug():
    """Class for the FPGA or Chip connected via a hyperdebug.
    Initializes OpenTitan with the provided firmware & provides helper functions.
    """
    def __init__(self, opentitantool, fw_bin, bitstream, tool_args):
        self.opentitantool = opentitantool
        self.fw_bin = fw_bin
        self.bitstream = bitstream
        self.tool_args = tool_args

    def initialize_target(self):
        # Programming the bitstream via the opentitantool seems to block
        # communication, programming it twice seems to solve the problem
        self.program_bitstream(self.bitstream)
        self.program_bitstream(self.bitstream)

        self.flash_target(self.fw_bin)

    def program_bitstream(self, bitstream, program_delay=2):
        if bitstream:
            bitstream_process = Popen(
                [
                    self.opentitantool,
                ] +
                self.tool_args +
                [
                    "--exec",
                    "transport init",
                    "--exec",
                    "fpga load-bitstream " + bitstream,
                    "no-op",
                ],
                stderr=PIPE,
            )
            stderr = bitstream_process.communicate()
            rc = bitstream_process.returncode
            if rc != 0:
                raise RuntimeError("Error: Failed to program the bitstream.")
                return 0
            else:
                stderr_str = stderr[1].decode('utf-8')
                if "Skip loading bitstream" not in stderr_str:
                    time.sleep(program_delay)
                print(f"Info: FPGA programmed with {bitstream}.")
        return 1

    def flash_target(self, firmware, boot_delay=2):
        flash_process = Popen(
            [
                self.opentitantool,
            ] +
            self.tool_args +
            [
                "--exec",
                "transport init",
                "--exec",
                "bootstrap " + firmware,
                "no-op",
            ],
            stdout=PIPE, stderr=PIPE
        )
        flash_process.communicate()
        rc = flash_process.returncode
        if rc != 0:
            raise RuntimeError("Error: Failed to flash chip.")
            return 0
        else:
            # Wait until chip finished booting.
            time.sleep(boot_delay)
            print(f"Info: Chip flashed with {firmware}.")
            return 1

    def init_communication(self, port, baudrate):
        """Open the communication interface.

        Configure OpenTitan on CW FPGA or the discrete chip.
        """
        com_interface = None
        if not port:
            port = self.find_target_port()
        com_interface = serial.Serial(port)
        com_interface.baudrate = baudrate
        # Setting a fixed 1s timeout for the UART connection.
        com_interface.timeout = 1
        return com_interface

    def find_target_port(self):
        for port in comports():
            if "UART2" in port.description and "HyperDebug" in port.description:
                return port.device
        print("Target not found!")
        return None

    def reset_target(self, com_reset: Optional[bool] = False, reset_delay=0.005):
        """Resets the target."""
        reset_process = Popen(
            [
                self.opentitantool,
            ] +
            self.tool_args +
            [
                "--exec",
                "transport init",
                "--exec",
                "gpio write RESET false",
                "--exec",
                "gpio write RESET true",
                "no-op",
            ],
            stdout=PIPE, stderr=PIPE
        )
        reset_process.communicate()
        rc = reset_process.returncode
        if rc != 0:
            raise RuntimeError("Error: Failed to reset chip.")
        else:
            time.sleep(reset_delay)
        if com_reset:
            self.com_interface = self.init_communication(None, 115200)
