# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import time
from subprocess import Popen, run, PIPE, CalledProcessError, TimeoutExpired
import select
import signal
import serial
import sys
import os
import socket
from serial.tools.list_ports import comports


class HyperDebug:
    """Class for the FPGA or Chip connected via a hyperdebug.
    Initializes OpenTitan with the provided firmware & provides helper functions.
    """

    def __init__(
        self,
        opentitantool,
        fw_bin,
        bitstream,
        tool_args,
        openocd,
        openocd_chip_config,
        openocd_design_config,
    ):
        self.opentitantool = opentitantool
        self.fw_bin = fw_bin
        self.bitstream = bitstream
        self.tool_args = tool_args
        self.openocd = openocd
        self.openocd_chip_config = openocd_chip_config
        self.openocd_design_config = openocd_design_config
        self.openocd_process = None

    def initialize_target(self, print_output=True):
        # Programming the bitstream via the opentitantool seems to block
        # communication, programming it twice seems to solve the problem
        self.program_bitstream(self.bitstream, print_output=print_output)
        self.program_bitstream(self.bitstream, print_output=print_output)

        self.flash_target(self.fw_bin, print_output=print_output)

        if self.openocd:
            self.start_openocd(print_output=print_output)

    def program_bitstream(self, bitstream, program_delay=2, print_output=True):
        if not bitstream:
            return

        command = (
            [self.opentitantool]
            + self.tool_args
            + ["--exec", "transport init", "--exec", f"fpga load-bitstream {bitstream}", "no-op"]
        )
        try:
            result = run(command, check=True, capture_output=True, text=True)
            if "Skip loading bitstream" not in result.stderr:
                time.sleep(program_delay)
            if print_output:
                print(f"Info: FPGA programmed with {bitstream}.")
        except CalledProcessError as e:
            print(f"Error: Failed to program the bitstream.\nStderr: {e.stderr}", file=sys.stderr)
            raise

    def flash_target(self, firmware, boot_delay=2, print_output=True):
        command = (
            [self.opentitantool]
            + self.tool_args
            + ["--exec", "transport init", "--exec", f"bootstrap {firmware}", "no-op"]
        )
        try:
            run(command, check=True, capture_output=True)
            # Wait until chip finishes booting.
            time.sleep(boot_delay)
            if print_output:
                print(f"Info: Chip flashed with {firmware}.")
        except CalledProcessError as e:
            print(f"Error: Failed to flash chip.\nStderr: {e.stderr}", file=sys.stderr)
            raise

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

    def start_openocd(self, startup_delay=4, print_output=True):
        self.close_openocd()
        # We set up OpenOCD with the following default ports
        # 6666 for tcl connections
        # 4444 for telnet connections
        # 3333 for gdb connections
        # You can adapt those ports, e.g., via adding the config: -c "telnet_port 4444"
        OPENOCD_COMMANDS = "adapter speed 500; transport select jtag; reset_config trst_only"

        command = [
            self.openocd,
            "-f",
            self.openocd_chip_config,
            "-c",
            OPENOCD_COMMANDS,
            "-f",
            self.openocd_design_config,
        ]

        if print_output:
            print("Starting OpenOCD", flush=True)

        self.openocd_process = Popen(command, stdin=PIPE, stdout=PIPE, stderr=PIPE)

        # OpenOCD provides its status data via the error output
        openocd_stderr = self.openocd_process.stderr.fileno()
        os.set_blocking(openocd_stderr, False)
        # Wait until the openocd is set up (this process will remain in the background)
        time.sleep(startup_delay)
        readable, _, _ = select.select([openocd_stderr], [], [], 0.1)
        if readable:
            try:
                data_after_wait = os.read(openocd_stderr, 1024 * 1024).decode(
                    "utf-8", errors="ignore"
                )
                if print_output:
                    print(data_after_wait, flush=True)
                if "Error:" in data_after_wait:
                    print("Error detected in starting openocd")

            except BlockingIOError:
                print("Error reading the openocd output")
                pass

    def close_openocd(self):
        if not self.openocd_process or self.openocd_process.poll() is not None:
            return

        self.openocd_process.send_signal(signal.SIGINT)
        try:
            self.openocd_process.communicate(timeout=10)
        except TimeoutExpired:
            self.openocd_process.kill()
            self.openocd_process.communicate()
        finally:
            self.openocd_process = None

    def read_openocd(self):
        if self.openocd_process:
            openocd_stderr = self.openocd_process.stderr.fileno()
            readable, _, _ = select.select([openocd_stderr], [], [], 0.1)
            if readable:
                try:
                    data = os.read(openocd_stderr, 1024 * 1024).decode("utf-8", errors="ignore")
                    return data

                except BlockingIOError:
                    print("Error reading the OpenOCD output")
                    pass
        return None

    def send_openocd_command(self, command, timeout=1.0, port=6666):
        HOST = "127.0.0.1"

        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(timeout)
            s.connect((HOST, port))
        except socket.error as e:
            print(f"Error connecting to OpenOCD on port {port}: {e}", flush=True)
            return f"ERROR: Connection failed: {e}"

        full_command = f"{command}\x1a"
        try:
            s.sendall(full_command.encode("utf-8"))

            response = b""
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                response += chunk
                if b"\x00" in chunk:
                    break

        except socket.timeout:
            print(f"Warning: Command '{command}' timed out after {timeout}s.", flush=True)
        except socket.error as e:
            print(f"Error sending/receiving data: {e}", flush=True)
            s.close()
            return f"ERROR: Send/Receive failed: {e}"

        s.close()

        decoded_response = response.decode("utf-8", errors="ignore").strip()

        if decoded_response.startswith(command):
            decoded_response = decoded_response[len(command):].strip()

        return decoded_response.strip()

    def find_target_port(self):
        for port in comports():
            if "UART2" in port.description and "HyperDebug" in port.description:
                return port.device
        print("Target not found!")
        return None

    def reset_target(self, com_reset=False, reset_delay=0.005):
        """Resets the target."""
        reset_process = (
            [self.opentitantool]
            + self.tool_args
            + [
                "--exec",
                "transport init",
                "--exec",
                "gpio write RESET false",
                "--exec",
                "gpio write RESET true",
                "no-op",
            ]
        )
        try:
            run(reset_process, check=True, capture_output=True, text=True)
            time.sleep(reset_delay)
        except CalledProcessError:
            print("Error: Failed to reset chip.")
            raise
        if com_reset:
            self.com_interface = self.init_communication(None, 115200)
