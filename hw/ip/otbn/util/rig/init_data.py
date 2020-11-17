# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Dict, List, Tuple


def gen_init_data(dmem_size: int) -> Dict[int, int]:
    '''Generate a dictionary with some initialised data

    This will be inserted into the program as initialised data (pre-loaded).
    The dictionary maps (word-aligned) byte addresses to u32 values.

    '''
    # Make sure to generate at least some 32-byte wide data for BN.LID calls,
    # but also generate some 4-byte wide stuff to make sure we do the right
    # thing from the start when loading a 4-byte word which has Xs above or
    # below it.
    assert dmem_size > 0

    init_data = {}
    for byte_width in [4, 32]:
        word_width = byte_width // 4
        hi_wword = dmem_size // byte_width - 1
        for blob_idx in range(random.randint(1, 4)):
            blob_wword = random.randint(0, hi_wword)
            blob_addr = byte_width * blob_wword
            for word_idx in range(word_width):
                init_data[blob_addr + 4 * word_idx] = random.getrandbits(32)

    return init_data


def init_data_to_json(init_data: Dict[int, int]) -> List[Tuple[int, int]]:
    '''Return init_data, as it should be serialized to json'''
    return [(addr, data) for addr, data in init_data.items()]


def read_init_data(parsed: object) -> Dict[int, int]:
    '''Read init_data as parsed from json'''
    if not isinstance(parsed, list):
        raise ValueError('init_data is not a list.')
    init_data = {}
    for idx, item in enumerate(parsed):
        if not (isinstance(item, list) and len(item) == 2):
            raise ValueError('Item {} of init_data is not a length 2 list.'
                             .format(item))
        addr, value = item

        if not (isinstance(addr, int) and isinstance(value, int)):
            raise ValueError('Item {} of init_data has addr or value '
                             'that is not an int.'
                             .format(idx))

        if addr < 0 or addr & 3:
            raise ValueError('Item {} of init_data has '
                             'an invalid address, 0x{:x}.'
                             .format(idx, addr))
        if not (0 <= value < (1 << 32)):
            raise ValueError('Item {} of init_data has '
                             'invalid data ({} is not a u32).'
                             .format(idx, value))

        init_data[addr] = value

    return init_data
