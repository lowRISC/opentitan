#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Simple Tool for FPGA SPI experiments
"""

import argparse
import logging as log
import os
import subprocess
import sys
import time

import pkg_resources  # part of setuptools
from pyftdi.spi import SpiController


def show_and_exit(clitool, packages):
    util_path = os.path.dirname(os.path.realpath(clitool))
    os.chdir(util_path)
    ver = subprocess.run(
        ["git", "describe", "--always", "--dirty", "--broken"],
        stdout=subprocess.PIPE).stdout.strip().decode('ascii')
    if (ver == ''):
        ver = 'not found (not in Git repository?)'
    sys.stderr.write(clitool + " Git version " + ver + '\n')
    for p in packages:
        sys.stderr.write(p + ' ' + pkg_resources.require(p)[0].version + '\n')
    exit(0)


USAGE = """
  spitest [options] text [text ...]
"""


def main():
    done_stdin = False
    parser = argparse.ArgumentParser(
        prog="spitest",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=__doc__)
    parser.add_argument(
        '--version', action='store_true', help='Show version and exit')
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Verbose output during processing')
    parser.add_argument(
        '-f',
        '--flippy',
        action='store_true',
        help='Flip the SPI/JTAG control GPIO 10 times and exit')
    parser.add_argument(
        '-l',
        '--length',
        type=int,
        action='store',
        help='Construct and send a message of specified length')
    parser.add_argument(
        '-j',
        '--jtag',
        action='store_true',
        help='Set SPI/JTAG control to JTAG and exit')
    parser.add_argument(
        'message',
        nargs='*',
        metavar='input',
        default='1234',
        help='message to send in 4 byte chunks')
    args = parser.parse_args()

    if args.version:
        show_and_exit(__file__, ["pyftdi"])

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Instanciate a SPI controller
    spi = SpiController(cs_count=1)

    # interfaces start from 1 here, so this is Channel A (called 0 in jtag)
    spi.configure('ftdi://ftdi:2232h/1')

    # Get a port to a SPI device w/ /CS on A*BUS3 and SPI mode 0 @ 1MHz
    device = spi.get_port(cs=0, freq=1E6, mode=0)

    # Get GPIO port to manage extra pins
    # BUS4 = JTAG TRST_N, BUS5 = JTAG SRST_N, BUS6 = JTAG_SPIN
    # Note: something makes FTDI default to BUS6 low, selected that for SPI
    # otherwise SRST being default low holds the chip in reset
    # pyftdi Set Direction also forces the output to zero
    # so initially make SRST an input w/pullup in FPGA in case SPI/JTAG was
    # initially JTAG
    gpio = spi.get_gpio()
    gpio.set_direction(0x40, 0x40)
    time.sleep(1)
    gpio.set_direction(0x70, 0x70)

    if args.jtag:
        gpio.write(0x70)
        return

    gpio.write(0x30)

    if args.flippy:
        for i in range(10):
            print("Select SPI")
            gpio.write(0x30)
            time.sleep(2)
            print("Select JTAG")
            gpio.write(0x70)
            time.sleep(2)
        return

    print("Select SPI")
    gpio.write(0x30)
    # Synchronous exchange with the remote SPI device
    if args.length:
        s = ''
        for i in range(args.length):
            s += hex(i & 15)[-1]
    else:
        s = ''
        for m in args.message:
            s += m + ' '
            s = s[:-1]  # remove extra space put on end
        # pad to ensure multiple of 4 bytes
        filled = len(s) % 4
        if filled:
            s += '....' [filled:]

    while len(s):
        write_buf = bytes(s[:4], encoding='utf8')
        read_buf = device.exchange(write_buf, duplex=True)
        print("Got " + str(read_buf))
        s = s[4:]


if __name__ == '__main__':
    main()
