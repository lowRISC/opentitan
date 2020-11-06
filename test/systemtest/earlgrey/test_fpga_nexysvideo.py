# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re

import pytest

from .. import config, utils

log = logging.getLogger(__name__)


@pytest.fixture(scope="module")
def localconf_nexysvideo(localconf):
    assert 'boards' in localconf
    assert 'nexysvideo' in localconf['boards']
    boardconf = localconf['boards']['nexysvideo']

    assert 'uart_device' in boardconf
    assert 'uart_speed' in boardconf
    return boardconf


@pytest.fixture(scope="module")
def uart_persistent(localconf_nexysvideo, tmp_path_factory):
    """
    A UART device connected to the FPGA board, which is kept active for
    for multiple tests.

    Use the `uart` fixture for per-test access to the UART device.
    """
    uart_device = localconf_nexysvideo['uart_device']
    uart_speed = localconf_nexysvideo['uart_speed']
    log_dir_path = tmp_path_factory.mktemp('uart')
    log.debug("Opening UART on device {} ({} baud)".format(
        uart_device, uart_speed))
    with utils.LoggingSerial(uart_device,
                             uart_speed,
                             timeout=1,
                             log_dir_path=log_dir_path,
                             default_filter_func=utils.
                             filter_remove_device_sw_log_prefix) as uart:

        yield uart


@pytest.fixture
def uart(uart_persistent, request):
    """ A UART device connected to the FPGA board.

    The UART is drained between test runs to give better isolation between the
    tests.
    """

    uart_persistent.log_add_marker("===== TEST {} START =====\n".format(
        request.node.name))

    yield uart_persistent

    # Read all remaining data from UART to have it available in the log file.
    uart_persistent.drain_in()

    uart_persistent.log_add_marker("===== TEST {} DONE =====\n\n".format(
        request.node.name))


@pytest.fixture(scope="module")
def nexysvideo_earlgrey(tmp_path_factory, topsrcdir, bin_dir,
                        localconf_nexysvideo):
    """ A Nexys Video board flashed with an Earl Grey bitstream """

    bitstream = bin_dir / "hw/top_earlgrey/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit"
    assert bitstream.is_file(), ("Bitstream not found at %s." % str(bitstream))

    cmd_pgm = [
        topsrcdir / 'util/opentitan-pgm-fpga/opentitan-pgm-fpga',
        'xc7a200tsbg484-1',
        bitstream,
    ]

    # Explicitly use a certain hardware server (if set)
    if 'hw_server_url' in localconf_nexysvideo:
        cmd_pgm += [
            '--hw-server-url',
            localconf_nexysvideo['hw_server_url'],
        ]

    log.debug("Flashing Nexys Video board with bitstream {}".format(
        str(bitstream)))
    tmp_path = tmp_path_factory.mktemp('nexysvideo_earlgrey')
    p_pgm = utils.Process(cmd_pgm, logdir=tmp_path, cwd=tmp_path)
    p_pgm.run()
    p_pgm.proc.wait(timeout=300)
    assert p_pgm.proc.returncode == 0


@pytest.fixture(params=config.TEST_APPS_SELFCHECKING,
                ids=lambda param: param['name'])
def app_selfchecking_bin(request, bin_dir):
    app_config = request.param

    if 'name' not in app_config:
        raise RuntimeError("Key 'name' not found in TEST_APPS_SELFCHECKING")

    if 'targets' in app_config and 'fpga_nexysvideo' not in app_config[
            'targets']:
        pytest.skip("Test %s skipped on NexysVideo FPGA." % app_config['name'])

    if 'binary_name' in app_config:
        binary_name = app_config['binary_name']
    else:
        binary_name = app_config['name']

    test_filename = binary_name + '_fpga_nexysvideo.bin'
    bin_path = bin_dir / 'sw/device/tests' / test_filename
    assert bin_path.is_file()
    return bin_path


def test_apps_selfchecking(tmp_path, localconf_nexysvideo, nexysvideo_earlgrey,
                           app_selfchecking_bin, bin_dir, uart):
    """ Load a simple application, and check its output. """

    spiflash = bin_dir / 'sw/host/spiflash/spiflash'
    utils.load_sw_over_spi(tmp_path, spiflash, app_selfchecking_bin)

    # We need to wait for this message to ensure we are asserting on the output
    # of the newly flashed software, not the software which might be already on
    # the chip (which might get re-executed when running spiflash).
    bootstrap_done_exp = b'Bootstrap: DONE!'
    assert uart.find_in_output(bootstrap_done_exp, timeout=60)

    bootmsg_exp = b'Boot ROM initialisation has completed, jump into flash!'
    assert uart.find_in_output(bootmsg_exp,
                               timeout=10), "End-of-bootrom string not found."

    log.debug("Waiting for pass string from device test")

    result_match = uart.find_in_output(re.compile(br'^(PASS|FAIL)!$'),
                                       timeout=60)
    assert result_match is not None, "PASS/FAIL indication not found in test output."

    result_msg = result_match.group(1)
    log.info("Test ended with {}".format(result_msg))
    assert result_msg == b'PASS'
