# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
from typing import List, Sequence

from shared.mem_layout import get_memory_layout

from .trace import Trace


class TraceDmemStore(Trace):
    def __init__(self, addr: int, value: int, is_wide: bool):
        self.addr = addr
        self.value = value
        self.is_wide = is_wide

    def trace(self) -> str:
        num_bytes = 32 if self.is_wide else 4
        top = self.addr + num_bytes - 1
        return 'dmem[{:#x}..{:#x}] = {:#x}'.format(self.addr, top, self.value)


class Dmem:
    '''An object representing OTBN's DMEM.

    Memory is stored as an array of 32-byte words (the native width for the
    OTBN wide side). These words are stored as 256-bit unsigned integers. This
    is the same width as the wide-side registers (to avoid unnecessary
    packing/unpacking work), but the unsigned values simplify tracing.

    '''

    def __init__(self) -> None:
        _, dmem_size = get_memory_layout()['DMEM']

        # Check the arguments look sensible, to avoid allocating massive chunks
        # of memory. We know we won't have more than 1 MiB of DMEM.
        if dmem_size > 1024 * 1024:
            raise RuntimeError('Implausibly large DMEM size: {}'
                               .format(dmem_size))

        # We're going to store DMEM as an array of 32-byte words (the native
        # width for the OTBN wide side). Of course, that means dmem_size needs
        # to be divisible by 32.
        if dmem_size % 32:
            raise RuntimeError('DMEM size ({}) is not divisible by 32.'
                               .format(dmem_size))

        num_words = dmem_size // 4

        # Initialise the memory to an arbitrary "bad" constant (here,
        # 0xdeadbeef). We could initialise to a random value, but maybe it's
        # more helpful to generate something recognisable for now.
        uninit = 0xdeadbeef

        self.data = [uninit] * num_words
        self.trace = []  # type: List[TraceDmemStore]

    def load_le_words(self, data: bytes) -> None:
        '''Replace the start of memory with data'''
        if len(data) > 32 * len(self.data):
            raise ValueError('Trying to load {} bytes of data, but DMEM '
                             'is only {} bytes long.'
                             .format(len(data), 32 * len(self.data)))
        # Zero-pad bytes up to the next multiple of 32 bits (because things
        # are little-endian, is like zero-extending the last word).
        if len(data) % 4:
            data = data + b'0' * (32 - (len(data) % 32))

        for idx32, u32 in enumerate(struct.iter_unpack('<I', data)):
            self.data[idx32] = u32[0]

    def dump_le_words(self) -> bytes:
        '''Return the contents of memory as bytes.

        The bytes are formatted as little-endian 32-bit words. These
        words are themselves packed little-endian into 256-bit words.

        '''
        u32s = [self.data[i] for i in range(len(self.data))]
        return struct.pack('<{}I'.format(len(u32s)), *u32s)

    def is_valid_256b_addr(self, addr: int) -> bool:
        '''Return true if this is a valid address for a BN.LID/BN.SID'''
        assert addr >= 0
        if addr & 31:
            return False

        word_addr = addr // 32
        if word_addr >= len(self.data):
            return False

        return True

    def load_u256(self, addr: int) -> int:
        '''Read a u256 little-endian value from an aligned address'''
        assert addr >= 0
        assert self.is_valid_256b_addr(addr)
        ret_data = 0
        for i in range(256 // 32):
            rd_data = self.data[(addr // 4) + i]
            ret_data = ret_data | (rd_data << (i * 32))

        return ret_data

    def store_u256(self, addr: int, value: int) -> None:
        '''Write a u256 little-endian value to an aligned address'''
        assert addr >= 0
        assert 0 <= value < (1 << 256)
        assert self.is_valid_256b_addr(addr)

        self.trace.append(TraceDmemStore(addr, value, True))

    def is_valid_32b_addr(self, addr: int) -> bool:
        '''Return true if this is a valid address for a LW/SW instruction'''
        assert addr >= 0
        if addr & 3:
            return False

        if (addr + 3) // 32 >= len(self.data):
            return False

        return True

    def load_u32(self, addr: int) -> int:
        '''Read a 32-bit value from memory.

        addr should be 4-byte aligned. The result is returned as an unsigned
        32-bit integer.

        '''
        assert addr >= 0
        assert self.is_valid_32b_addr(addr)

        return self.data[addr // 4]

    def store_u32(self, addr: int, value: int) -> None:
        '''Store a 32-bit unsigned value to memory.

        addr should be 4-byte aligned.

        '''
        assert addr >= 0
        assert 0 <= value <= (1 << 32) - 1
        assert self.is_valid_32b_addr(addr)

        self.trace.append(TraceDmemStore(addr, value, False))

    def changes(self) -> Sequence[Trace]:
        return self.trace

    def _commit_store(self, item: TraceDmemStore) -> None:
        if item.is_wide:
            assert 0 <= item.value < (1 << 256)
            mask = (1 << 32) - 1
            for i in range(256 // 32):
                wr_data = (item.value >> (i * 32)) & mask
                self.data[(item.addr // 4) + i] = wr_data

            return
        else:
            self.data[item.addr // 4] = item.value

        assert 0 <= item.value <= (1 << 32) - 1

    def commit(self) -> None:
        for item in self.trace:
            self._commit_store(item)
        self.trace = []

    def abort(self) -> None:
        self.trace = []
