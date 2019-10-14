#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Runs a binary on the verilated system, which is expected to write
one of "PASS!\r\n" or "FAIL!\r\n" to UART to determine success or failure.
Failing to write either will result in a timeout.

This test requires some configuration options. Use the following steps to
run the test manually after building Verilator and the sw/boot_rom and
sw/examples/hello_world targets.

$ cd ${REPO_TOP}
$ pytest -s -v test/systemtest/functional_verilator_test.py \
  --test_bin sw/tests/hmac/sw.vmem \
  --rom_bin sw/boot_rom/rom.vmem \
  --verilator_model build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator
"""

import logging
import os
from pathlib import Path
import re
import select
import subprocess
import time

import pytest

import test_utils

logging.basicConfig(level=logging.DEBUG)


class TestFunctionalVerilator:
    """
    Execute a test binary in a Verilator-simulated hardware build, using UART
    output to validate test success or failure.
    """
    @pytest.fixture
    def sim_top_earlgrey(self, tmp_path, sim_top_build, sw_test_bin, rom_bin):
        assert Path(sw_test_bin).is_file()
        assert Path(rom_bin).is_file()
        assert Path(sim_top_build).is_file()

        cmd_sim = [
            str(Path(sim_top_build).resolve()), '--flashinit',
            str(Path(sw_test_bin).resolve()), '--rominit',
            str(Path(rom_bin).resolve())
        ]
        p_sim = test_utils.Process(cmd_sim,
                                   logdir=str(tmp_path),
                                   cwd=str(tmp_path),
                                   startup_done_expect='Simulation running',
                                   startup_timeout=10)
        p_sim.run()

        yield p_sim

        p_sim.terminate()

    def test_execute_binary(self, sim_top_earlgrey, uart_timeout):
        """
        Executes the binary and inspects its UART for "PASS!\r\n" or "FAIL!\r\n".
        """

        logger = logging.getLogger(__name__)

        # Verilator will print the string "UART: created /dev/pts/#" to
        # indicate which pseudoterminal the UART port is bound to.
        uart_match = sim_top_earlgrey.find_in_output(
            re.compile('UART: Created (/dev/pts/\\d+)'), 5)

        assert uart_match != None
        uart_path = uart_match.group(1)
        logger.info("Found UART port at %s." % uart_path)

        # Now, open the UART device and read line by line until we pass or
        # fail.
        with open(uart_path, 'rb') as uart_device:
            uart_fd = uart_device.fileno()
            pattern = re.compile('.*?(PASS!\r\n|FAIL!\r\n)')
            match = test_utils.stream_fd_to_log(uart_fd, logger, pattern,
                                                uart_timeout)
            if match == None:
                pytest.fail('Deadline exceeded: did not see PASS! or FAIL! within %ds.', uart_timeout)

            if match.group(1) == 'PASS!\r\n':
                logger.debug('Got PASS! from binary.')
            else:
                pytest.fail('Got FAIL! from binary.')
