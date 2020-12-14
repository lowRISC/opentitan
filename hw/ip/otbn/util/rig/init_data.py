# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Dict, List, Tuple


class InitData:
    '''Initialised data, written to the random binary to be loaded.'''
    def __init__(self, values: Dict[int, int]):
        self._values = values

    def as_segs(self) -> Dict[int, List[int]]:
        '''Convert from dictionary representation to segments

        The dictionary representation is keyed by 4-byte aligned addresses and
        has values 32-bit unsigned numbers. The segment representation maps
        4-byte aligned base addresses to lists of 32-bit unsigned numbers (and
        the segments are disjoint).

        '''
        segs = {}
        cur_seg = None

        for addr, value in self._values.items():
            assert addr & 3 == 0
            assert 0 <= value < (1 << 32)

            if cur_seg is not None:
                base_addr, next_addr, values = cur_seg
                if addr == next_addr:
                    values.append(value)
                    cur_seg = (base_addr, next_addr + 4, values)
                    continue

                assert base_addr not in segs
                segs[base_addr] = values
                cur_seg = None

            assert cur_seg is None
            cur_seg = (addr, addr + 4, [value])

        if cur_seg is not None:
            base_addr, next_addr, values = cur_seg
            assert base_addr not in segs
            segs[base_addr] = values

        return segs

    def as_json(self) -> List[Tuple[int, int]]:
        '''Return init_data, as it should be serialized to json'''
        return [(addr, data) for addr, data in self._values.items()]

    def keys(self) -> List[int]:
        return list(self._values.keys())

    @staticmethod
    def read(parsed: object) -> 'InitData':
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

        return InitData(init_data)

    @staticmethod
    def gen(dmem_size: int) -> 'InitData':
        '''Generate some initialised data

        This will be inserted into the program as initialised data (pre-loaded).
        The dictionary maps (word-aligned) byte addresses to u32 values.

        '''
        assert dmem_size > 0

        values = {}
        byte_width = 32
        word_width = byte_width // 4
        hi_wword = dmem_size // byte_width - 1
        for blob_idx in range(random.randint(1, 4)):
            blob_wword = random.randint(0, hi_wword)
            blob_addr = byte_width * blob_wword
            for word_idx in range(word_width):
                values[blob_addr + 4 * word_idx] = random.getrandbits(32)

        return InitData(values)
