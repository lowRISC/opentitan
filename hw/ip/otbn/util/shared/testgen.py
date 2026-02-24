# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import random
from typing import Callable, Dict, Optional, TextIO

_GPR_NAMES = [f'x{i}' for i in range(32)]
_WDR_NAMES = [f'w{i}' for i in range(32)]


def itoa_dmem(value: bytes) -> str:
    ''' Convert an integer (in the form of a bytearray) to a DMEM hexstring for
        usage in HJSON testcase files. '''
    s = ''
    for b in value:
        s = f'{int(b):02x}' + s
    return '0x' + s


def itoa_gpr(value: bytes) -> str:
    ''' Convert an integer (in the form of a bytearray) to a GPR hexstring for
        usage in Exp or HJSON testcase files.. '''
    if len(value) > 8:
        raise ValueError(f'Expected value is too large: {value}')
    v = int.from_bytes(value, byteorder='little')
    return f'{v:#010x}'


def itoa_wdr(value: bytes) -> str:
    ''' Convert an integer (in the form of a bytearray) to a WDR hexstring for
        usage in Exp or HJSON testcase files.. '''
    if len(value) > 32:
        raise ValueError(f'Expected value is too large: {value}')
    v = int.from_bytes(value, byteorder='little')
    return f'{v:#066x}'


def write_test_data(inputs: Dict[str, bytes], data_file: TextIO) -> None:
    '''Write the test input data to DMEM.'''
    data_file.write('.data\n')
    for name in inputs:
        data_file.write('\n')
        if len(inputs[name]) <= 4:
            # Buffer should be read as a 32-bit (4-byte) value.
            align = 4
            length = 4
        else:
            # Buffer should be read as a (sequence of) 256-bit (32-byte) values.
            align = 32
            length = ((len(inputs[name]) + 31) // 32) * 32
        data_file.write(f'.balign {align}\n')
        data_file.write(f'.globl {name}\n')
        data_file.write(f'{name}:\n')
        for i in range(0, length, 4):
            word = int.from_bytes(inputs[name][i:i + 4], byteorder='little')
            data_file.write(f'.word {word:#010x}\n')


def write_test_exp(exp: Dict[str, bytes], exp_file: TextIO) -> None:
    '''Write the expected-values file for the test.'''
    for name in exp:
        if name in _GPR_NAMES or name == 'ERR_BITS':
            exp_file.write(f'{name} = {itoa_gpr(exp[name])}\n')
        elif name in _WDR_NAMES:
            exp_file.write(f'{name} = {itoa_wdr(exp[name])}\n')
        else:
            raise ValueError(f'Register name {name} not recognized.')


def testcase(gen: Callable[[Optional[int]], Dict]) -> None:
    '''Generic entry point for the creation of arbitrary autogen testcases.
       Parses the command line arguments and invokes the provided callback
       function that generates the HJSON dictionary.'''
    def generate():
        parser = argparse.ArgumentParser()
        parser.add_argument('-s', '--seed',
                            type=int,
                            required=False,
                            help=('Seed value for pseudorandomness.'))
        parser.add_argument('hjson',
                            metavar='FILE',
                            type=argparse.FileType('w'),
                            help=('Testcase HJSON file.'))
        args = parser.parse_args()

        if args.seed is not None:
            random.seed(args.seed)

        json.dump(gen(), args.hjson)

    return generate
