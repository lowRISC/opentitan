# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import os
import shutil
import subprocess
from pathlib import Path

import pytest
import yaml

from . import utils

log = logging.getLogger(__name__)


@pytest.hookimpl(tryfirst=True)
def pytest_exception_interact(node, call, report):
    """Dump all log files in case of a test failure."""
    try:
        if not report.failed:
            return
        if 'tmp_path_factory' not in node.funcargs:
            return
    except Exception:
        return

    utils.dump_temp_files(node.funcargs['tmp_path_factory'].getbasetemp())


@pytest.fixture(scope="session")
def localconf():
    """Host-local configuration."""
    if 'OPENTITAN_TEST_LOCALCONF' in os.environ:
        localconf_yaml_file = Path(os.environ['OPENTITAN_TEST_LOCALCONF'])
        log.info("Attempting to use configuration file set in "
                 "OPENTITAN_TEST_LOCALCONF.")
    else:
        XDG_CONFIG_HOME = Path(os.getenv(
            'XDG_CONFIG_HOME', os.path.join(os.environ['HOME'], '.config')))
        localconf_yaml_file = XDG_CONFIG_HOME / 'opentitan' / 'test-localconf.yaml'

    log.info('Reading configuration from ' + str(localconf_yaml_file))

    with open(str(localconf_yaml_file), 'r') as fp:
        return yaml.load(fp, Loader=yaml.SafeLoader)


@pytest.fixture(scope="session")
def topsrcdir():
    """Return the top-level source directory as Path object."""
    # TODO: Consider making this configurable using a pytest arg.
    path = (Path(os.path.dirname(__file__)) / '..' / '..').resolve()
    assert path.is_dir()
    return path


@pytest.fixture(scope="session")
def bin_dir(topsrcdir):
    """ Return the BIN_DIR (build output directory) """
    if 'BIN_DIR' in os.environ:
        bin_dir = Path(os.environ['BIN_DIR'])
        log.info("Using build outputs from environment variable BIN_DIR={}".format(str(bin_dir)))
    else:
        bin_dir = topsrcdir / 'build-bin'
        log.info("Using build outputs from $REPO_TOP/build-bin ({})".format(str(bin_dir)))

    assert bin_dir.is_dir()
    return bin_dir


@pytest.fixture(scope="session")
def openocd():
    """ Return the path to the openocd binary. """
    openocd_bin = shutil.which('openocd')
    assert openocd_bin

    proc = subprocess.run([openocd_bin, '--version'],
                          check=True,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,
                          encoding="utf8")
    log.info("Using OpenOCD at {}: '{}'".format(openocd_bin,
                                                proc.stdout.splitlines()[0]))
    return Path(openocd_bin)


def pytest_configure(config):
    config.addinivalue_line("markers", "slow: mark test as slow, will be excluded from the main "
                                       "verilator job in CI")


@pytest.fixture(scope="module")
def uart_persistent(localconf_board, tmp_path_factory):
    """
    A UART device connected to the FPGA board, which is kept active for
    for multiple tests.

    Use the `uart` fixture for per-test access to the UART device.
    """
    uart_device = localconf_board['uart_device']
    uart_speed = localconf_board['uart_speed']
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
