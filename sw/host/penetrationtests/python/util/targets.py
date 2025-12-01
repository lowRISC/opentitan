# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional
from dataclasses import dataclass
import time

from sw.host.penetrationtests.python.util.hyperdebug import HyperDebug


@dataclass
class TargetConfig:
    """Target configuration.
    Stores information about the target.
    """

    target_type: str
    fw_bin: str
    interface_type: Optional[str] = None
    pll_frequency: Optional[int] = None
    bitstream: Optional[str] = None
    force_program_bitstream: Optional[bool] = False
    port: Optional[str] = None
    read_timeout: Optional[int] = 1
    tool_args: Optional[str] = None
    opentitantool: Optional[str] = None
    usb_serial: Optional[str] = None
    husky_serial: Optional[str] = None
    openocd: Optional[str] = None
    openocd_chip_config: Optional[str] = (None,)
    openocd_design_config: Optional[str] = None


class Target:
    """Target class.

    Represents a SCA/FI target. Currently, ChipWhisperer FPGA boards
    or the discrete OpenTitan chip are supported.
    """

    # This is a fixed baudrate.
    baudrate = 115200
    # Due to a bug in the UART of the CW340, we need to send each byte separately
    # and add a small timeout before sending the next one.
    # This contains the calculation of the delay.
    pacing = 10 / baudrate

    def __init__(self, target_cfg: TargetConfig):
        self.target_cfg = target_cfg

        self.target = None
        # Currently, we only consider hyperdebug interfaces
        if target_cfg.interface_type == "hyperdebug":
            self.target = HyperDebug(
                target_cfg.opentitantool,
                target_cfg.fw_bin,
                target_cfg.bitstream,
                target_cfg.tool_args,
                target_cfg.openocd,
                target_cfg.openocd_chip_config,
                target_cfg.openocd_design_config,
            )

        self.com_interface = self.target.init_communication(target_cfg.port, self.baudrate)

    def initialize_target(self, print_output=True):
        self.target.initialize_target(print_output=print_output)
        # Clear the UART
        self.dump_all()

    def reset_target(self, reset_delay=0.005):
        self.target.reset_target(reset_delay=reset_delay)

    def write(self, data):
        """Write data to the target."""
        if "fpga" in self.target_cfg.target_type:
            # Sleep one uart character time after writing to the uart to pace characters into the
            # usb-serial device for CW340 so that we don't fill any device-internal buffers.
            for byte in data:
                self.com_interface.write(bytes([byte]))
                time.sleep(self.pacing)
        else:
            self.com_interface.write(data)

    def readline(self):
        """read line."""
        return self.com_interface.readline()

    def print_all(self, max_tries=50):
        it = 0
        while it != max_tries:
            try:
                read_line = str(self.readline().decode().strip())
                if len(read_line) > 0:
                    print(read_line, flush=True)
                else:
                    break
            except UnicodeDecodeError:
                pass
            it += 1

    def read_all(self, max_tries=50):
        it = 0
        response = ""
        while it != max_tries:
            try:
                read_line = str(self.readline().decode().strip())
                if len(read_line) > 0:
                    response += read_line
                else:
                    return response
            except UnicodeDecodeError:
                pass
            it += 1

    def dump_all(self, max_tries=50):
        it = 0
        while it != max_tries:
            read_line = str(self.readline())
            if len(read_line) <= 5:
                break
            it += 1

    def check_fault_or_read_reponse(self, max_tries=50):
        """
        Args:
            max_tries: Maximum number of attempts to read from UART.

        Returns:
            - The JSON response of OpenTitan or the line containing FAULT.
            - True if the chip gave a response, False if it ran into a fault.
        """
        it = 0
        while it != max_tries:
            try:
                read_line = str(self.readline())
                if "FAULT" in read_line:
                    return read_line, False
                if "RESP_OK" in read_line:
                    return read_line.split("RESP_OK:")[1].split(" CRC:")[0], True
                it += 1
            except UnicodeDecodeError:
                it += 1
                continue
        return "", False

    def check_reset_or_read_reponse(self, max_tries=50):
        """
        Args:
            max_tries: Maximum number of attempts to read from UART.

        Returns:
            - The JSON response of OpenTitan or the line containing Chip flashed.
            - True if the chip gave a response, False if the chip resetted.
        """
        it = 0
        while it != max_tries:
            try:
                read_line = str(self.readline())
                if "Chip flashed" in read_line:
                    return read_line, False
                if "RESP_OK" in read_line:
                    return read_line.split("RESP_OK:")[1].split(" CRC:")[0], True
                it += 1
            except UnicodeDecodeError:
                it += 1
                continue
        return "", False

    def read_response(self, max_tries: Optional[int] = 50):
        """
        Args:
            max_tries: Maximum number of attempts to read from UART.

        Returns:
            The JSON response of OpenTitan.
        """
        it = 0
        while it < max_tries:
            try:
                read_line = str(self.readline().decode().strip())
            except UnicodeDecodeError:
                break
            if len(read_line) > 0:
                if "RESP_OK" in read_line:
                    return read_line.split("RESP_OK:")[1].split(" CRC:")[0]
            else:
                break
            it += 1
        return ""

    def start_openocd(self, startup_delay=4, print_output=True):
        if self.target_cfg.openocd:
            self.target.start_openocd(startup_delay=startup_delay, print_output=print_output)

    def read_openocd(self):
        if self.target_cfg.openocd:
            return self.target.read_openocd()

    def close_openocd(self):
        if self.target_cfg.openocd:
            self.target.close_openocd()

    def send_openocd_command(self, command):
        if self.target_cfg.openocd:
            return self.target.send_openocd_command(command)
