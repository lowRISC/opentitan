#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Runs OpenOCD compliance test against Verilator target.

This test requires some configuration options. Use the following steps to run
the test manually after building Verilator and the boot_rom and hello_world
targets.

$ cd ${REPO_TOP}
$ pytest -s -v test/systemtest/openocd_verilator_test.py \
  --test_bin hello_world.elf \
  --rom_bin boot_rom.elf \
  --verilator_model build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator

In some cases the pytest environment may not be able to find the openocd binary.
To work around this issue, run the test with an additional configuration option:

  --openocd /tools/openocd/bin/openocd
"""

import logging
import re
import subprocess
import time
import pytest

import test_utils

logging.basicConfig(level=logging.DEBUG)

class TestCoreVerilator:
    """Test core functionality in a Verilator-simulated hardware build."""

    @pytest.fixture
    def sim_top_earlgrey(self, tmp_path, sim_top_build, sw_test_bin, rom_bin):
        cmd_sim = [
            str(sim_top_build),
            '--meminit=flash,' + str(sw_test_bin),
            '--meminit=rom,' + str(rom_bin)
        ]
        p_sim = test_utils.Process(
            cmd_sim,
            logdir=str(tmp_path),
            cwd=str(tmp_path),
            startup_done_expect='Simulation running',
            startup_timeout=10)
        p_sim.run()

        yield p_sim

        p_sim.terminate()

    def test_openocd_riscv_compliancetest(self, tmp_path, sim_top_earlgrey,
                                          topsrcdir, openocd):
        """Run RISC-V Debug compliance test built into OpenOCD."""
        assert subprocess.call([str(openocd), '--version']) == 0
        cmd_openocd = [
            str(openocd),
            '-s', str(topsrcdir / 'util' / 'openocd'),
            '-f', 'board/lowrisc-earlgrey-verilator.cfg',
            '-c', 'init; riscv test_compliance; shutdown'
        ]
        p_openocd = test_utils.Process(
            cmd_openocd, logdir=str(tmp_path), cwd=str(tmp_path))
        p_openocd.run()

        logging.getLogger(__name__).info(
            "OpenOCD should terminate itself; give it up to 5 minutes")
        p_openocd.proc.wait(timeout=300)
        assert p_openocd.proc.returncode == 0

        logging.getLogger(__name__).info(
            "Now wait 60 seconds until the program has finished execution")
        time.sleep(60)

        try:
            p_openocd.terminate()
        except ProcessLookupError:
            # process is already dead
            pass
