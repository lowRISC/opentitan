# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, TextIO

_GPR_NAMES = [f'x{i}' for i in range(32)]
_WDR_NAMES = [f'w{i}' for i in range(32)]


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
        value = int.from_bytes(exp[name], byteorder='little')
        if name in _GPR_NAMES or name == 'ERR_BITS':
            if len(exp[name]) > 8:
                raise ValueError(f'Expected value for {name} is too large: {value}')
            exp_file.write(f'{name} = {value:#010x}\n')
        elif name in _WDR_NAMES:
            if len(exp[name]) > 32:
                raise ValueError(f'Expected value for {name} is too large: {value}')
            exp_file.write(f'{name} = {value:#066x}\n')
        else:
            raise ValueError(f'Register name {name} not recognized.')
