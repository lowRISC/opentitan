#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Runs a binary on the verilated system, which is expected to write
one of "PASS!\r\n" or "FAIL!\r\n" to UART to determine success or failure.
Failing to write either will result in a timeout.

This test requires some configuration options. Use the following steps to run
the test manually after building a Verilator simulation and the device boot ROM
and a device software target.

$ cd ${REPO_TOP}
$ pytest -s -v test/systemtest/functional_verilator_test.py \
  --test_bin sw.elf \
  --rom_bin boot_rom.elf \
  --verilator_model build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator
"""

import logging
import re
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
        cmd_sim = [
            str(sim_top_build),
            '--meminit=flash,' + str(sw_test_bin),
            '--meminit=rom,' + str(rom_bin)
        ]
        p_sim = test_utils.Process(cmd_sim,
                                   logdir=str(tmp_path),
                                   cwd=str(tmp_path),
                                   startup_done_expect='Simulation running',
                                   startup_timeout=10)
        p_sim.run()

        yield p_sim

        p_sim.terminate()

    @pytest.mark.timeout(120)
    def test_execute_binary(self, sim_top_earlgrey, uart_timeout, logfile):
        """
        Executes the binary and inspects its UART for "PASS!\r\n" or "FAIL!\r\n".
        """

        logger = logging.getLogger(__name__)
        test_utils.setup_logfile(logger, logfile)


        # Verilator will print the string "UART: created /dev/pts/#" to
        # indicate which pseudoterminal the UART port is bound to.
        uart_match = sim_top_earlgrey.find_in_output(
            re.compile('UART: Created (/dev/pts/\\d+)'), 5)

        assert uart_match is not None
        uart_path = uart_match.group(1)
        logger.info("Found UART port at %s." % uart_path)

        # Now, open the UART device and read line by line until we pass or
        # fail.
        with open(uart_path, 'rb') as uart_device:
            uart_fd = uart_device.fileno()
            pattern = re.compile('.*?(PASS!\r\n|FAIL!\r\n)')
            match = test_utils.stream_fd_to_log(uart_fd, logger, pattern,
                                                uart_timeout)
            assert match is not None, ('Deadline exceeded: did not see PASS! or FAIL! within %ds.' % uart_timeout)

            assert match.group(1).strip() == 'PASS!'
