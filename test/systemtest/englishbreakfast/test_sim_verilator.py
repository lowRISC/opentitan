# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import pytest

from . import config
from .. import test_sim_verilator_opentitan as ot


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

    test_filename = binary_name + '_sim_verilator.64.scr.vmem'
    bin_path = bin_dir / test_dir / test_filename
    assert bin_path.is_file()

    return (bin_path, verilator_extra_args)


def test_apps_selfchecking(tmp_path, bin_dir, app_selfchecking):
    """
    Run a self-checking application on a English Breakfast Verilator simulation

    The ROM is initialized with the default boot ROM, the flash is initialized
    with |app_selfchecking|.

    Self-checking applications are expected to return PASS or FAIL in the end.
    """

    sim_path = bin_dir / "hw/top_englishbreakfast/Vchip_englishbreakfast_verilator"
    rom_vmem_path = (bin_dir /
            "sw/device/lib/testing/test_rom/test_rom_sim_verilator.32.vmem")

    sim = ot.VerilatorSimOpenTitan(sim_path, rom_vmem_path, None, tmp_path)

    sim.run(app_selfchecking[0], extra_sim_args=app_selfchecking[1])

    ot.assert_selfchecking_test_passes(sim)

    sim.terminate()
