# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import re

import pytest

from .. import config, utils

log = logging.getLogger(__name__)


@pytest.fixture(scope="module")
def localconf_board(localconf):
    assert 'boards' in localconf
    assert 'cw310' in localconf['boards']
    boardconf = localconf['boards']['cw310']

    assert 'uart_device' in boardconf
    assert 'uart_speed' in boardconf
    return boardconf


@pytest.fixture(scope="module")
def board_earlgrey(tmp_path_factory, topsrcdir, bin_dir, localconf_board):
    """ A ChipWhispere CW310 board flashed with an Earl Grey bitstream """

    bitstream = bin_dir / "hw/top_earlgrey/lowrisc_systems_chip_earlgrey_cw310_0.1.bit"
    assert bitstream.is_file(), ("Bitstream not found at %s." % str(bitstream))

    cmd_pgm = [
        topsrcdir / 'util/fpga/cw310_loader.py',
        '--bitstream',
        bitstream,
    ]

    log.debug("Flashing ChipWhisperer CW310 board with bitstream {}".format(
        str(bitstream)))
    tmp_path = tmp_path_factory.mktemp('cw310_earlgrey')
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

    if 'targets' in app_config and 'fpga_cw310' not in app_config[
            'targets']:
        pytest.skip("Test %s skipped on ChipWhisperer CW310 board." % app_config['name'])

    if 'binary_name' in app_config:
        binary_name = app_config['binary_name']
    else:
        binary_name = app_config['name']

    test_filename = binary_name + '_fpga_nexysvideo.bin'
    bin_path = bin_dir / 'sw/device/tests' / test_filename
    assert bin_path.is_file()
    return bin_path


def test_apps_selfchecking(tmp_path, localconf_board, board_earlgrey,
                           app_selfchecking_bin, topsrcdir, bin_dir, uart):
    """ Load a simple application, and check its output. """

    loader_path = topsrcdir / 'util/fpga/cw310_loader.py'
    utils.load_sw_over_spi(tmp_path,
                           loader_path,
                           app_selfchecking_bin,
                           timeout=30)

    # We need to wait for this message to ensure we are asserting on the output
    # of the newly flashed software, not the software which might be already on
    # the chip (which might get re-executed when running the loading tool).
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
