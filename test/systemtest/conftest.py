#!/usr/bin/env python3
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


def pytest_addoption(parser):
    """Test harness configuration options."""
    parser.addoption("--test_bin", action="store", default="")
    parser.addoption("--rom_bin", action="store", default="")
    parser.addoption("--verilator_model", action="store", default="")
    parser.addoption("--openocd", action="store", default="openocd")
    parser.addoption("--uart_timeout", action="store", default="60")
    parser.addoption("--fpga_uart", action="store", default="")
    parser.addoption("--spiflash", action="store", default="")
    parser.addoption("--log", action="store", default="")

@pytest.hookimpl(tryfirst=True)
def pytest_exception_interact(node, call, report):
    """Dump all log files in case of a test failure."""
    try:
        if not report.failed:
            return
        if not 'tmp_path' in node.funcargs:
            return
    except:
        return

    tmp_path = str(node.funcargs['tmp_path'])
    print("\n\n")
    print("================= DUMP OF ALL TEMPORARY FILES =================")

    for f in os.listdir(tmp_path):
        f_abs = os.path.join(tmp_path, f)
        if not os.path.isfile(f_abs):
            continue
        print("vvvvvvvvvvvvvvvvvvvv {} vvvvvvvvvvvvvvvvvvvv".format(f))
        with open(f_abs, 'r') as fp:
            print(fp.read())
        print("^^^^^^^^^^^^^^^^^^^^ {} ^^^^^^^^^^^^^^^^^^^^\n\n".format(f))


@pytest.fixture(scope="session")
def localconf(request):
    """Host-local configuration."""
    if os.getenv('OPENTITAN_TEST_LOCALCONF') and os.path.isfile(
            os.environ['OPENTITAN_TEST_LOCALCONF']):
        localconf_yaml_file = os.environ['OPENTITAN_TEST_LOCALCONF']
    else:
        XDG_CONFIG_HOME = os.getenv(
            'XDG_CONFIG_HOME', os.path.join(os.environ['HOME'], '.config'))
        localconf_yaml_file = os.path.join(XDG_CONFIG_HOME, 'opentitan',
                                           'test-localconf.yaml')
    logging.getLogger(__name__).info('Reading configuration from ' +
                                     localconf_yaml_file)

    with open(str(localconf_yaml_file), 'r') as fp:
        return yaml.load(fp)


@pytest.fixture(scope="session")
def topsrcdir(request):
    """Return the top-level source directory as Path object."""
    # TODO: Consider making this configurable using a pytest arg.
    path = (Path(os.path.dirname(__file__)) / '..' / '..').resolve()
    assert path.is_dir()
    return path


@pytest.fixture(scope="session")
def sw_test_bin(pytestconfig):
    """Return path to software test binary."""
    path = Path(pytestconfig.getoption('test_bin')).resolve()
    assert path.is_file()
    return path

@pytest.fixture(scope="session")
def rom_bin(pytestconfig):
    """Return path to boot_rom binary."""
    path = Path(pytestconfig.getoption('rom_bin')).resolve()
    assert path.is_file()
    return path


@pytest.fixture(scope="session")
def sim_top_build(pytestconfig):
    """Return path to Verilator sim model."""
    path = Path(pytestconfig.getoption('verilator_model')).resolve()
    assert path.is_file()
    return path


@pytest.fixture(scope="session")
def openocd(pytestconfig):
    """Return path to OpenOCD executable."""
    path = Path(pytestconfig.getoption('openocd'))
    # TODO: Require that the OpenOCD executable be passed as a command-line
    # argument in the future, rather than relying on $PATH lookup.
    # assert path.is_file()
    return path

@pytest.fixture(scope="session")
def uart_timeout(pytestconfig):
    """Return the timeout in seconds for UART to print PASS."""
    return int(pytestconfig.getoption('uart_timeout'))

@pytest.fixture(scope="session")
def fpga_uart(pytestconfig):
    """Return the path to the UART attached to the FPGA."""
    path = Path(pytestconfig.getoption('fpga_uart')).resolve()
    assert path.exists() and not path.is_dir()
    return path

@pytest.fixture(scope="session")
def spiflash(pytestconfig):
    """Return the path to the spiflash executable."""
    path = Path(pytestconfig.getoption('spiflash')).resolve()
    assert path.is_file()
    return path

@pytest.fixture(scope="session")
def logfile(pytestconfig):
    """Return path to logfile."""
    log = pytestconfig.getoption('log')
    if not log:
        return
    # The strict option is only availabe on python 3.6
    # CI currently uses >=3.5.2
    # Turns out however even not using resolve doesn't work.
    # The logging function in 3.5 uses os.path.isabs to check whether
    # path is absolute and does not accept POSIXPATH objects
    # path = Path(log).resolve(strict=False)
    # assert not path.is_dir()

    path = os.path.abspath(log)
    assert not os.path.isdir(path)
    return path
