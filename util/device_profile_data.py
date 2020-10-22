#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Parse device output to extract LLVM profile data.

The profile data obtained from the device is raw. Thus, it must be indexed
before it can be used to generate coverage reports.

Typical usage:
    stty -F /dev/ttyUSB0 icanon
    cat /dev/ttyUSB0 | ./device_profile_data.py foo.profraw
    llvm-profdata merge -sparse foo.profraw -o foo.profdata
    llvm-cov show OBJECT_FILE -instr-profile=foo.profdata
"""
import argparse
import zlib
import re
import sys


def extract_profile_data(device_output_file):
    """Parse device output to extract LLVM profile data.

    This function returns the LLVM profile data as a byte array after
    verifying its length and checksum.

    Args:
        device_output_file: File that contains the device output.
    Returns:
        LLVM profile data.
    Raises:
        ValueError: If LLVM profile data cannot be detected in the device
            output or its length or checksum is incorrect.
    """
    lines = device_output_file.read().decode('utf-8', 'ignore').splitlines()
    for i, line in zip(reversed(range(len(lines))), reversed(lines)):
        match = re.match(
            r"""
                LLVM\ profile\ data
                \ \(length:\ (?P<length>\d*),
                \ CRC32:\ (?P<checksum>[0-9A-F]*)\):
            """, line, re.VERBOSE)
        if match:
            exp_length = int(match.group('length'))
            exp_checksum = match.group('checksum')
            byte_array = bytes.fromhex(lines[i + 1])
            break
    # Check if output has LLVM profile data
    if not match:
        raise ValueError(
            'Could not detect the LLVM profile data in device output.')
    # Check length
    act_length = len(byte_array)
    if act_length != exp_length:
        raise ValueError(('Length check failed! ',
                          f'Expected: {exp_length}, actual: {act_length}.'))
    # Check checksum
    act_checksum = zlib.crc32(byte_array).to_bytes(4,
                                                   byteorder='little',
                                                   signed=False).hex().upper()
    if act_checksum != exp_checksum:
        raise ValueError(
            ('Checksum check failed! ',
             f'Expected: {exp_checksum}, actual: {act_checksum}.'))
    return byte_array


def main():
    """Parses command line arguments and extracts the profile data from device
    output."""
    argparser = argparse.ArgumentParser(
        description='Extract LLVM profile data from device output.')
    argparser.add_argument(dest='output_file',
                           type=argparse.FileType('wb'),
                           default=sys.stdout,
                           help='output file for writing LLVM profile data')
    argparser.add_argument('--input_file',
                           type=argparse.FileType('rb'),
                           default=sys.stdin.buffer,
                           help='device output')
    args = argparser.parse_args()

    args.output_file.write(extract_profile_data(args.input_file))


if __name__ == '__main__':
    main()
