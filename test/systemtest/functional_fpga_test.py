#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Runs a binary on an FPGA,  which is expected to write
one of "PASS!\r\n" or "FAIL!\r\n" to the UART to determine success or failure.
Failing to write either will result in a timeout.

This test requires some setup and some configuration. This test expects you
to have:
  - A supported FPGA connected to your workstation.
  - That FPGA must be flashed with a synthesized EarlGrey bitfile, which has
    been spliced with the OpenTitan bootloader.
  - A prebuilt spiflash executable.

You must then provide this test with the .bin file for the test, the UART
device path for the FPGA, and the spiflash executable. For example:

$ cd ${REPO_TOP}
$ pytest -s -v test/systemtest/functional_fpga_test.py \
  --test_bin sw/device/tests/hmac/sw.bin \
  --fpga_uart /dev/ttyUSB2 \
  --spiflash sw/host/spiflash/spiflash
"""

import logging
from pathlib import Path
import re

import pytest

import test_utils

logging.basicConfig(level=logging.DEBUG)


class TestFunctionalFpga:
    """
    Execute a test binary on a locally connected FPGA, using UART
    output to validate test success or failure.
    """
    @pytest.fixture
    def spiflash_proc(self, tmp_path, spiflash, sw_test_bin):
        cmd_flash = [str(spiflash), '--input', str(sw_test_bin)]
        p_flash = test_utils.Process(cmd_flash,
                                   logdir=str(tmp_path),
                                   cwd=str(tmp_path),
                                   startup_done_expect='Running SPI flash update.',
                                   startup_timeout=10)
        p_flash.run()

        yield p_flash

        p_flash.terminate()

    def test_execute_binary(self, spiflash_proc, fpga_uart, uart_timeout, logfile):
        """
        Executes the binary and inspects its UART for "PASS!\r\n" or "FAIL!\r\n".
        """

        logger = logging.getLogger(__name__)
        test_utils.setup_logfile(logger, logfile)


        # Open the UART device and read line by line until we pass or fail.
        with fpga_uart.open('rb') as uart_device:
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
