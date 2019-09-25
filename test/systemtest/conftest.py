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


@pytest.hookimpl(tryfirst=True)
def pytest_exception_interact(node, call, report):
    """Dump all log files in case of a test failure."""
    try:
        if not report.failed:
            return
        if not 'tmpdir' in node.funcargs:
            return
    except:
        return

    tmpdir = str(node.funcargs['tmpdir'])
    print("\n\n")
    print("================= DUMP OF ALL TEMPORARY FILES =================")

    for f in os.listdir(tmpdir):
        f_abs = os.path.join(tmpdir, f)
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
    return str(Path(os.path.dirname(__file__)) / '..' / '..')


@pytest.fixture(scope="session")
def sw_test_bin(pytestconfig):
    """Return path to software test binary."""
    return pytestconfig.getoption('test_bin')


@pytest.fixture(scope="session")
def rom_bin(pytestconfig):
    """Return path to boot_rom binary."""
    return pytestconfig.getoption('rom_bin')


@pytest.fixture(scope="session")
def sim_top_build(pytestconfig):
    """Return path to Verilator sim model."""
    return pytestconfig.getoption('verilator_model')


@pytest.fixture(scope="session")
def openocd(pytestconfig):
    """Return path to OpenOCD executable."""
    return pytestconfig.getoption('openocd')
