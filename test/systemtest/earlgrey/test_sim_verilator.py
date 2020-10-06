# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re
from pathlib import Path

import pytest

from .. import config, utils

log = logging.getLogger(__name__)


class VerilatorSimEarlgrey:
    UART0_SPEED = 9600  # see device/lib/arch/device_sim_verilator.c

    def __init__(self, sim_path: Path, rom_elf_path: Path, work_dir: Path):
        """ A verilator simulation of the Earl Grey toplevel """
        assert sim_path.is_file()
        self._sim_path = sim_path

        assert rom_elf_path.is_file()
        self._rom_elf_path = rom_elf_path

        assert work_dir.is_dir()
        self._work_dir = work_dir

        self._log = logging.getLogger(__name__)

        self._uart0_log = None
        self.uart0_log_path = None
        self.spi0_log_path = None

    def run(self, flash_elf=None):
        """
        Run the simulation
        """

        self.uart0_log_path = self._work_dir / 'uart0.log'

        cmd_sim = [
            self._sim_path, '--meminit=rom,' + str(self._rom_elf_path),
            '+UARTDPI_LOG_uart0=' + str(self.uart0_log_path)
        ]

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
        # UART
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

    def find_in_uart0(self,
                      pattern,
                      timeout,
                      filter_func=None,
                      from_start=False):
        assert self._uart0_log

        if filter_func is None:
            # The default filter function for all device software in OpenTitan.
            filter_func = utils.filter_remove_device_sw_log_prefix

        return utils.find_in_files([self._uart0_log],
                                   pattern,
                                   timeout,
                                   filter_func=filter_func,
                                   from_start=from_start)


@pytest.fixture(params=config.TEST_APPS_SELFCHECKING_SIM_VERILATOR)
def app_selfchecking_elf(request, bin_dir):
    """ A self-checking device application as ELF for Verilator simulation """

    test_filename = request.param + '_sim_verilator.elf'
    bin_path = bin_dir / 'sw/device/tests' / test_filename
    assert bin_path.is_file()
    return bin_path


# The following tests use the UART output from the log file written by the
# UARTDPI module, and not the simulated UART device (/dev/pty/N) to ensure
# reliable testing: As soon as the device application finishes, the simulation
# ends and the UART device becomes unavailable to readers.
# Therefore, if we do not read quickly enough, we miss the PASS/FAIL indication
# and the test never finishes.


def test_apps_selfchecking(tmp_path, bin_dir, app_selfchecking_elf):
    """
    Run a self-checking application on a Earl Grey Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    with |app_selfchecking_elf|.

    Self-checking applications are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_earlgrey/Vtop_earlgrey_verilator"
    rom_elf_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.elf"

    sim = VerilatorSimEarlgrey(sim_path, rom_elf_path, tmp_path)

    sim.run(app_selfchecking_elf)

    bootmsg_exp = b'Boot ROM initialisation has completed, jump into flash!'
    assert sim.find_in_uart0(
        bootmsg_exp,
        timeout=120) is not None, "End-of-bootrom string not found."

    log.debug("Waiting for pass string from device test")

    result_match = sim.find_in_uart0(re.compile(rb'^(PASS|FAIL)!$'),
                                     timeout=240)
    assert result_match is not None, "PASS/FAIL indication not found in test output."

    result_msg = result_match.group(1)
    log.info("Test ended with {}".format(result_msg))
    assert result_msg == b'PASS'

    sim.terminate()


@pytest.mark.skip(reason="Spiflash on Verilator isn't reliable currently. See issue #3708.")
def test_spiflash(tmp_path, bin_dir):
    """ Load a single application to the Verilator simulation using spiflash """

    sim_path = bin_dir / "hw/top_earlgrey/Vtop_earlgrey_verilator"
    rom_elf_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.elf"

    sim = VerilatorSimEarlgrey(sim_path, rom_elf_path, tmp_path)
    sim.run()

    log.debug("Waiting for simulation to be ready for SPI input")
    spiwait_msg = b'HW initialisation completed, waiting for SPI input...'
    assert sim.find_in_uart0(spiwait_msg, timeout=120)

    log.debug("SPI is ready, continuing with spiload")
    app_bin = bin_dir / 'sw/device/tests/dif_uart_sanitytest_sim_verilator.bin'
    spiflash = bin_dir / 'sw/host/spiflash/spiflash'
    utils.load_sw_over_spi(tmp_path, spiflash, app_bin,
                           ['--verilator', sim.spi0_device_path])

    bootmsg_exp = b'Boot ROM initialisation has completed, jump into flash!'
    assert sim.find_in_uart0(
        bootmsg_exp,
        timeout=600) is not None, "End-of-bootrom string not found."

    log.debug("Waiting for pass string from device test")

    result_match = sim.find_in_uart0(re.compile(rb'^(PASS|FAIL)!$'),
                                     timeout=240)
    assert result_match is not None, "PASS/FAIL indication not found in test output."

    result_msg = result_match.group(1)
    log.info("Test ended with {}".format(result_msg))
    assert result_msg == b'PASS'

    sim.terminate()
