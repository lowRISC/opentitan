# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re
import subprocess
from pathlib import Path

import pytest

from .. import config, utils

log = logging.getLogger(__name__)


class VerilatorSimEarlgrey:
    UART0_SPEED = 7200  # see device/lib/arch/device_sim_verilator.c

    def __init__(self, sim_path: Path, rom_elf_path: Path,
                 otp_img_path: Path, work_dir: Path):
        """ A verilator simulation of the Earl Grey toplevel """
        assert sim_path.is_file()
        self._sim_path = sim_path

        self.p_sim = None

        assert rom_elf_path.is_file()
        assert otp_img_path.is_file()
        self._rom_elf_path = rom_elf_path
        self._otp_img_path = otp_img_path

        assert work_dir.is_dir()
        self._work_dir = work_dir

        self._log = logging.getLogger(__name__)

        self._uart0_log = None
        self.uart0_log_path = None
        self.spi0_log_path = None

    def run(self, flash_elf=None, extra_sim_args=[]):
        """
        Run the simulation
        """

        self.uart0_log_path = self._work_dir / 'uart0.log'

        cmd_sim = [
            self._sim_path,
            '--meminit=rom,' + str(self._rom_elf_path),
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


@pytest.fixture(params=config.TEST_APPS_SELFCHECKING,
                ids=lambda param: param['name'])
def app_selfchecking(request, bin_dir):
    """ A self-checking device application for Verilator simulation

    Returns:
        A set (elf_path, verilator_extra_args)
    """

    app_config = request.param

    if 'name' not in app_config:
        raise RuntimeError("Key 'name' not found in TEST_APPS_SELFCHECKING")

    if 'targets' in app_config and 'sim_verilator' not in app_config['targets']:
        pytest.skip("Test %s skipped on Verilator." % app_config['name'])

    if 'binary_name' in app_config:
        binary_name = app_config['binary_name']
    else:
        binary_name = app_config['name']

    if 'verilator_extra_args' in app_config:
        verilator_extra_args = app_config['verilator_extra_args']
    else:
        verilator_extra_args = []

    test_filename = binary_name + '_sim_verilator.elf'
    bin_path = bin_dir / 'sw/device/tests' / test_filename
    assert bin_path.is_file()

    return (bin_path, verilator_extra_args)


# The following tests use the UART output from the log file written by the
# UARTDPI module, and not the simulated UART device (/dev/pty/N) to ensure
# reliable testing: As soon as the device application finishes, the simulation
# ends and the UART device becomes unavailable to readers.
# Therefore, if we do not read quickly enough, we miss the PASS/FAIL indication
# and the test never finishes.


def assert_selfchecking_test_passes(sim):
    assert sim.find_in_output(
        re.compile(r"SW test transitioned to SwTestStatusInTest.$"),
        timeout=120,
        filter_func=utils.filter_remove_sw_test_status_log_prefix
    ) is not None, "Start of test indication not found."

    log.debug("Waiting for pass string from device test")

    result_match = sim.find_in_output(
        re.compile(r'^==== SW TEST (PASSED|FAILED) ====$'),
        timeout=600,
        filter_func=utils.filter_remove_sw_test_status_log_prefix)
    assert result_match is not None, "PASSED/FAILED indication not found in test output."

    result_msg = result_match.group(1)
    log.info("Test ended with {}".format(result_msg))
    assert result_msg == 'PASSED'


def test_apps_selfchecking(tmp_path, bin_dir, app_selfchecking):
    """
    Run a self-checking application on a Earl Grey Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    with |app_selfchecking|.

    Self-checking applications are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_earlgrey/Vtop_earlgrey_verilator"
    rom_elf_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.elf"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = VerilatorSimEarlgrey(sim_path, rom_elf_path, otp_img_path, tmp_path)

    sim.run(app_selfchecking[0], extra_sim_args=app_selfchecking[1])

    assert_selfchecking_test_passes(sim)

    sim.terminate()


@pytest.mark.skip(
    reason="Spiflash on Verilator isn't reliable currently. See issue #3708.")
def test_spiflash(tmp_path, bin_dir):
    """ Load a single application to the Verilator simulation using spiflash """

    sim_path = bin_dir / "hw/top_earlgrey/Vtop_earlgrey_verilator"
    rom_elf_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.elf"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = VerilatorSimEarlgrey(sim_path, rom_elf_path, otp_img_path, tmp_path)
    sim.run()

    log.debug("Waiting for simulation to be ready for SPI input")
    spiwait_msg = b'HW initialisation completed, waiting for SPI input...'
    assert sim.find_in_uart0(spiwait_msg, timeout=120)

    log.debug("SPI is ready, continuing with spiload")
    app_bin = bin_dir / 'sw/device/tests/dif_uart_smoketest_sim_verilator.bin'
    spiflash = bin_dir / 'sw/host/spiflash/spiflash'
    utils.load_sw_over_spi(tmp_path, spiflash, app_bin,
                           ['--verilator', sim.spi0_device_path])

    assert_selfchecking_test_passes(sim)

    sim.terminate()


def test_openocd_basic_connectivity(tmp_path, bin_dir, topsrcdir, openocd):
    """Test the basic connectivity to the system through OpenOCD

    Run earlgrey in Verilator, connect to it via OpenOCD, and check that the
    JTAG TAP, the harts, etc. are found as expected. No further interaction
    with the core or the system (bus) is performed.
    """
    # Run a simulation (bootrom only, no app beyond that)
    sim_path = bin_dir / "hw/top_earlgrey/Vtop_earlgrey_verilator"
    rom_elf_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.elf"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = VerilatorSimEarlgrey(sim_path, rom_elf_path, otp_img_path, tmp_path)
    sim.run()

    # Wait a bit until the system has reached the bootrom and a first arbitrary
    # message has been printed to UART.
    assert sim.find_in_uart0(re.compile(rb'.*I00000'), 120,
                             filter_func=None), "No UART log message found."

    # Run OpenOCD to connect to design and then shut down again immediately.
    cmd_openocd = [
        openocd, '-s',
        str(topsrcdir / 'util' / 'openocd'), '-f',
        'board/lowrisc-earlgrey-verilator.cfg', '-c', 'init; shutdown'
    ]
    p_openocd = utils.Process(cmd_openocd, logdir=tmp_path, cwd=tmp_path)
    p_openocd.run()

    # Look for a message indicating that the right JTAG TAP was found.
    msgs_exp = [
        ('Info : JTAG tap: riscv.tap tap/device found: 0x04f5484d '
         '(mfg: 0x426 (Google Inc), part: 0x4f54, ver: 0x0)'),
        'Info : Examined RISC-V core; found 1 harts',
        'Info :  hart 0: XLEN=32, misa=0x40101104',
    ]

    for msg_exp in msgs_exp:
        msg = p_openocd.find_in_output(msg_exp, 1, from_start=True)
        assert msg is not None, "Did not find message {!r} in OpenOCD output".format(
            msg_exp)

    p_openocd.proc.wait(timeout=120)
    try:
        p_openocd.terminate()
    except ProcessLookupError:
        # OpenOCD process is already dead
        pass
    assert p_openocd.proc.returncode == 0

    # End Verilator simulation
    sim.terminate()
