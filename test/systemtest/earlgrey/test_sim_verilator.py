# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re

import pytest

from . import config, silicon_creator_config, roms_config
from .. import utils
from .. import test_sim_verilator_opentitan as ot

log = logging.getLogger(__name__)


@pytest.fixture(params=roms_config.TEST_ROMS_SELFCHECKING,
                ids=lambda param: param['name'])
def rom_selfchecking(request, bin_dir):
    """ A self-checking ROM image for Verilator simulation

    Returns:
        A set (image_path, verilator_extra_args)
    """

    rom_config = request.param

    if 'name' not in rom_config:
        raise RuntimeError("Key 'name' not found in TEST_ROMS_SELFCHECKING")

    if 'targets' in rom_config and 'sim_verilator' not in rom_config['targets']:
        pytest.skip("Test %s skipped on Verilator." % rom_config['name'])

    if 'binary_name' in rom_config:
        binary_name = rom_config['binary_name']
    else:
        binary_name = rom_config['name']

    if 'verilator_extra_args' in rom_config:
        verilator_extra_args = rom_config['verilator_extra_args']
    else:
        verilator_extra_args = []

    # Allow tests to optionally specify their subdir within the project.
    test_dir = rom_config.get('test_dir', 'sw/device/tests')

    test_filename = binary_name + '_sim_verilator.scr.39.vmem'
    bin_path = bin_dir / test_dir / test_filename
    assert bin_path.is_file()

    return (bin_path, verilator_extra_args)


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

    # Allow tests to optionally specify their subdir within the project.
    test_dir = app_config.get('test_dir', 'sw/device/tests')

    test_filename = binary_name + '_sim_verilator.elf'
    bin_path = bin_dir / test_dir / test_filename
    assert bin_path.is_file()

    return (bin_path, verilator_extra_args)


@pytest.fixture(
    params=silicon_creator_config.TEST_SILICON_CREATOR_APPS_SELFCHECKING,
    ids=lambda param: param['name'])
def app_silicon_creator_selfchecking(request, bin_dir):
    """ A self-checking device application for Verilator simulation

    Returns:
        A set (elf_path, verilator_extra_args)
    """

    app_config = request.param

    if not all(key in app_config for key in ('name', 'signing_key')):
        raise RuntimeError(
            "One or more required keys ('name', 'signing_key') not found in"
            " TEST_APPS_SILICON_CREATOR_SELFCHECKING")

    if 'targets' in app_config and 'sim_verilator' not in app_config['targets']:
        pytest.skip("Test %s skipped on Verilator." % app_config['name'])

    if 'verilator_extra_args' in app_config:
        verilator_extra_args = app_config['verilator_extra_args']
    else:
        verilator_extra_args = []

    test_filename = 'rom_ext_{}_sim_verilator.{}.signed.64.vmem'.format(
        app_config['name'], app_config['signing_key'])
    bin_path = bin_dir / 'sw/device/tests' / test_filename
    assert bin_path.is_file()

    return (bin_path, verilator_extra_args)


# The following tests use the UART output from the log file written by the
# UARTDPI module, and not the simulated UART device (/dev/pty/N) to ensure
# reliable testing: As soon as the device application finishes, the simulation
# ends and the UART device becomes unavailable to readers.
# Therefore, if we do not read quickly enough, we miss the PASS/FAIL indication
# and the test never finishes.


def test_roms_selfchecking(tmp_path, bin_dir, rom_selfchecking):
    """
    Run a self-checking ROM image on a Earl Grey Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    to zero.

    Self-checking ROMs are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_earlgrey/Vchip_earlgrey_verilator"
    rom_vmem_path = rom_selfchecking[0]
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = ot.VerilatorSimOpenTitan(sim_path, rom_vmem_path, otp_img_path, tmp_path)

    sim.run(flash_elf=None, extra_sim_args=rom_selfchecking[1])

    ot.assert_selfchecking_test_passes(sim)

    sim.terminate()


def test_apps_selfchecking(tmp_path, bin_dir, app_selfchecking):
    """
    Run a self-checking application on a Earl Grey Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    with |app_selfchecking|.

    Self-checking applications are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_earlgrey/Vchip_earlgrey_verilator"
    rom_vmem_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = ot.VerilatorSimOpenTitan(sim_path, rom_vmem_path, otp_img_path, tmp_path)

    sim.run(app_selfchecking[0], extra_sim_args=app_selfchecking[1])

    ot.assert_selfchecking_test_passes(sim)

    sim.terminate()


@pytest.mark.slow
def test_apps_selfchecking_silicon_creator(tmp_path, bin_dir,
                                           app_silicon_creator_selfchecking):
    """
    Run a self-checking application on a Earl Grey Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    with |app_selfchecking|.

    Self-checking applications are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_earlgrey/Vchip_earlgrey_verilator"
    rom_vmem_path = bin_dir / ("sw/device/silicon_creator/mask_rom/"
                               "mask_rom_sim_verilator.scr.39.vmem")
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    # Use a longer timeout for boot due to the overhead of signature verification.
    sim = ot.VerilatorSimOpenTitan(sim_path,
                                   rom_vmem_path,
                                   otp_img_path,
                                   tmp_path,
                                   boot_timeout=55 * 60)

    sim.run(app_silicon_creator_selfchecking[0],
            extra_sim_args=app_silicon_creator_selfchecking[1])

    ot.assert_selfchecking_test_passes(sim)

    sim.terminate()


@pytest.mark.skip(
    reason="Spiflash on Verilator isn't reliable currently. See issue #3708.")
def test_spiflash(tmp_path, bin_dir):
    """ Load a single application to the Verilator simulation using spiflash """

    sim_path = bin_dir / "hw/top_earlgrey/Vchip_earlgrey_verilator"
    rom_vmem_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = ot.VerilatorSimOpenTitan(sim_path, rom_vmem_path, otp_img_path, tmp_path)
    sim.run()

    log.debug("Waiting for simulation to be ready for SPI input")
    spiwait_msg = b'HW initialisation completed, waiting for SPI input...'
    assert sim.find_in_uart0(spiwait_msg, timeout=120)

    log.debug("SPI is ready, continuing with spiload")
    app_bin = bin_dir / 'sw/device/tests/uart_smoketest_sim_verilator.bin'
    spiflash = bin_dir / 'sw/host/spiflash/spiflash'
    utils.load_sw_over_spi(tmp_path, spiflash, app_bin,
                           ['--verilator', sim.spi0_device_path])

    ot.assert_selfchecking_test_passes(sim)

    sim.terminate()


def test_openocd_basic_connectivity(tmp_path, bin_dir, topsrcdir, openocd):
    """Test the basic connectivity to the system through OpenOCD

    Run earlgrey in Verilator, connect to it via OpenOCD, and check that the
    JTAG TAP, the harts, etc. are found as expected. No further interaction
    with the core or the system (bus) is performed.
    """
    # Run a simulation (bootrom only, no app beyond that)
    sim_path = bin_dir / "hw/top_earlgrey/Vchip_earlgrey_verilator"
    rom_vmem_path = bin_dir / "sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem"
    otp_img_path = bin_dir / "sw/device/otp_img/otp_img_sim_verilator.vmem"

    sim = ot.VerilatorSimOpenTitan(sim_path, rom_vmem_path, otp_img_path, tmp_path)
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
