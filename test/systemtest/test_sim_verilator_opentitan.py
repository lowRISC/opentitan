# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re
import subprocess
from pathlib import Path

from . import utils

log = logging.getLogger(__name__)


class VerilatorSimOpenTitan:
    UART0_SPEED = 7200  # see device/lib/arch/device_sim_verilator.c

    def __init__(self,
                 sim_path: Path,
                 rom_vmem_path: Path,
                 otp_img_path: Path,
                 work_dir: Path,
                 boot_timeout: int = 4*60,
                 test_timeout: int = 20*60):
        """ A verilator simulation of an OpenTitan toplevel """
        assert sim_path.is_file()
        self._sim_path = sim_path

        self.p_sim = None

        assert rom_vmem_path.is_file()
        self._rom_vmem_path = rom_vmem_path
        assert otp_img_path is None or otp_img_path.is_file()
        self._otp_img_path = otp_img_path

        assert work_dir.is_dir()
        self._work_dir = work_dir

        self.boot_timeout = boot_timeout
        self.test_timeout = test_timeout

        self._log = logging.getLogger(__name__)

        self._uart0_log = None
        self.uart0_log_path = None
        self.spi0_log_path = None

    def run(self, flash_elf=None, extra_sim_args=[]):
        """
        Run the simulation
        """

        self.uart0_log_path = self._work_dir / 'uart0.log'

        if self._otp_img_path is None:
            cmd_sim = [
                self._sim_path, '--meminit=rom,' + str(self._rom_vmem_path),
                '+UARTDPI_LOG_uart0=' + str(self.uart0_log_path)
            ]
        else:
            cmd_sim = [
                self._sim_path, '--meminit=rom,' + str(self._rom_vmem_path),
                '--meminit=otp,' + str(self._otp_img_path),
                '+UARTDPI_LOG_uart0=' + str(self.uart0_log_path)
            ]
        cmd_sim += extra_sim_args

        if flash_elf is not None:
            assert flash_elf.is_file()
            cmd_sim.append('--meminit=flash,' + str(flash_elf))

        self.p_sim = utils.Process(cmd_sim,
                                   logdir=self._work_dir,
                                   cwd=self._work_dir,
                                   startup_done_expect='Simulation running',
                                   startup_timeout=10)
        self.p_sim.run()

        self._log.info("Simulation running")

        # Find paths to simulated I/O devices
        # UART (through the simulated terminal)
        self._uart0 = None
        uart0_match = self.p_sim.find_in_output(
            re.compile(r'UART: Created (/dev/pts/\d+) for uart0\.'),
            timeout=1,
            from_start=True)
        assert uart0_match is not None
        self.uart0_device_path = Path(uart0_match.group(1))
        assert self.uart0_device_path.is_char_device()
        self._log.debug("Found uart0 device file at {}".format(
            str(self.uart0_device_path)))

        # UART0 as logged directly to file by the uartdpi module.
        assert self.uart0_log_path.is_file()
        self._uart0_log = open(str(self.uart0_log_path), 'rb')

        # SPI
        spi0_match = self.p_sim.find_in_output(
            re.compile(r'SPI: Created (/dev/pts/\d+) for spi0\.'),
            timeout=1,
            from_start=True)
        assert spi0_match is not None
        self.spi0_device_path = Path(spi0_match.group(1))
        assert self.spi0_device_path.is_char_device()
        self._log.debug("Found spi0 device file at {}".format(
            str(self.spi0_device_path)))

        self.spi0_log_path = self._work_dir / 'spi0.log'
        assert self.spi0_log_path.is_file()

        # GPIO
        self.gpio0_fifo_write_path = self._work_dir / 'gpio0-write'
        assert self.gpio0_fifo_write_path.is_fifo()

        self.gpio0_fifo_read_path = self._work_dir / 'gpio0-read'
        assert self.gpio0_fifo_read_path.is_fifo()

        self._log.info("Simulation startup completed.")

    def uart0(self):
        if self._uart0 is None:
            log_dir_path = self._work_dir / 'uart0'
            log_dir_path.mkdir()
            log.info("Opening UART on device {} ({} baud)".format(
                str(self.uart0_device_path), self.UART0_SPEED))
            self._uart0 = utils.LoggingSerial(
                str(self.uart0_device_path),
                self.UART0_SPEED,
                timeout=1,
                log_dir_path=log_dir_path,
                default_filter_func=utils.filter_remove_device_sw_log_prefix)

        return self._uart0

    def terminate(self):
        """ Gracefully terminate the simulation """
        if self._uart0 is not None:
            self._uart0.close()

        if self._uart0_log is not None:
            self._uart0_log.close()

        self.p_sim.send_ctrl_c()

        # Give the process some time to clean up
        self.p_sim.proc.wait(timeout=5)
        assert self.p_sim.proc.returncode == 0

        try:
            self.p_sim.terminate()
        except ProcessLookupError:
            # process is already dead
            pass

    def find_in_output(self,
                       pattern,
                       timeout,
                       filter_func=None,
                       from_start=False):
        """ Find a pattern in STDOUT or STDERR of the Verilator simulation """
        assert self.p_sim

        return self.p_sim.find_in_output(pattern,
                                         timeout,
                                         from_start=from_start,
                                         filter_func=filter_func)

    def find_in_uart0(self,
                      pattern,
                      timeout,
                      filter_func=utils.filter_remove_device_sw_log_prefix,
                      from_start=False):
        assert self._uart0_log

        try:
            return utils.find_in_files([self._uart0_log],
                                       pattern,
                                       timeout,
                                       filter_func=filter_func,
                                       from_start=from_start)
        except subprocess.TimeoutExpired:
            return None


# The following tests use the UART output from the log file written by the
# UARTDPI module, and not the simulated UART device (/dev/pty/N) to ensure
# reliable testing: As soon as the device application finishes, the simulation
# ends and the UART device becomes unavailable to readers.
# Therefore, if we do not read quickly enough, we miss the PASS/FAIL indication
# and the test never finishes.


def assert_selfchecking_test_passes(sim):
    assert sim.find_in_output(
        re.compile(r"SW test transitioned to SwTestStatusInTest.$"),
        timeout=sim.boot_timeout,
        filter_func=utils.filter_remove_sw_test_status_log_prefix
    ) is not None, "Start of test indication not found."

    log.debug("Waiting for pass string from device test")

    result_match = sim.find_in_output(
        re.compile(r'^==== SW TEST (PASSED|FAILED) ====$'),
        timeout=sim.test_timeout,
        filter_func=utils.filter_remove_sw_test_status_log_prefix)
    assert result_match is not None, "PASSED/FAILED indication not found in test output."

    result_msg = result_match.group(1)
    log.info("Test ended with {}".format(result_msg))
    assert result_msg == 'PASSED'
