# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
from typing import List

from shared.mem_layout import get_memory_layout

from riscvmodel.types import Trace  # type: ignore


class TraceDmemStore(Trace):  # type: ignore
    def __init__(self, addr: int, value: int, is_wide: bool):
        self.addr = addr
        self.value = value
        self.is_wide = is_wide

    def __str__(self) -> str:
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

        # Sanity check to avoid allocating massive chunks of memory. We know we
        # won't have more than 1 MiB of DMEM.
        if dmem_size > 1024 * 1024:
            raise RuntimeError('Implausibly large DMEM size: {}'
                               .format(dmem_size))

        # We're going to store DMEM as an array of 32-byte words (the native
        # width for the OTBN wide side). Of course, that means dmem_size needs
        # to be divisible by 32.
        if dmem_size % 32:
            raise RuntimeError('DMEM size ({}) is not divisible by 32.'
                               .format(dmem_size))

        num_words = dmem_size // 32

        # Initialise the memory to an arbitrary "bad" constant (here,
        # 0xdeadbeef). We could initialise to a random value, but maybe it's
        # more helpful to generate something recognisable for now.
        uninit = 0
        for i in range(32 // 4):
            uninit = (uninit << 32) | 0xdeadbeef

        self.data = [uninit] * num_words
        self.trace = []  # type: List[Trace]

    def _get_u32s(self, idx: int) -> List[int]:
        '''Return the value at idx as 8 32-bit unsigned integers'''
        assert 0 <= idx < len(self.data)

        word = self.data[idx]
        assert 0 <= word <= 1 << 256

        # Pack this unsigned word into w32s as 8 32-bit numbers. Note that
        # this packing is "big-endian": the first unsigned word contains
        # the MSB of the value (as its LSB).
        ret = []
        w32_mask = (1 << 32) - 1
        for subidx in range(8):
            ret.append((word >> (32 * (7 - subidx))) & w32_mask)
        return ret

    def _set_u32s(self, idx: int, u32s: List[int]) -> None:
        '''Set the value at idx with 8 32-bit unsigned integers'''
        assert 0 <= idx < len(self.data)
        assert len(u32s) == 8

        # Accumulate the u32s into a 256-bit unsigned number (in a big-endian
        # fashion)
        u256 = 0
        for u32 in u32s:
            assert 0 <= u32 <= (1 << 32) - 1
            u256 = (u256 << 32) | u32

        # Store it!
        self.data[idx] = u256

    def load_le_words(self, data: bytes) -> None:
        '''Replace the start of memory with data

        This data should be in the form of little-endian 32-bit words. These
        words are themselves packed little-endian into 256-bit words.

        '''
        if len(data) > 32 * len(self.data):
            raise ValueError('Trying to load {} bytes of data, but DMEM '
                             'is only {} bytes long.'
                             .format(len(data), 32 * len(self.data)))

        # Zero-pad bytes up to the next multiple of 256 bits (because things
        # are little-endian, is like zero-extending the last word).
        if len(data) % 32:
            data = data + b'0' * (32 - (len(data) % 32))

        acc = []
        for idx32, u32 in enumerate(struct.iter_unpack('<I', data)):
            acc.append(u32[0])
            if len(acc) == 8:
                # Reverse acc here, because we're also little-endian moving
                # from u32 to u256
                acc.reverse()
                self._set_u32s(idx32 // 8, acc)
                acc = []

        # Our zero-extension should have guaranteed we finished on a multiple
        # of 8, but it can't hurt to check.
        assert acc == []

    def dump_le_words(self) -> bytes:
        '''Return the contents of memory as bytes.

        The bytes are formatted as little-endian 32-bit words. These
        words are themselves packed little-endian into 256-bit words.

        '''
        u32s = []
        for idx in range(len(self.data)):
            # As in load_le_words, we also have to reverse each set of 8 words
            # because we're little-endian at this scale too.
            u32s += reversed(self._get_u32s(idx))
        return struct.pack('<{}I'.format(len(u32s)), *u32s)

    def load_i256(self, addr: int) -> int:
        '''Read a wide word from memory. addr should be aligned.'''
        assert 0 == addr % 32
        u256 = self.data[addr // 32]
        i256 = u256 - (1 << 256) if u256 >> 255 else u256
        assert -(1 << 255) <= i256 <= (1 << 255) - 1
        return i256

    def store_i256(self, addr: int, value: int) -> None:
        '''Write a wide word to memory. addr should be aligned.'''
        assert 0 == addr % 32
        assert -(1 << 255) <= value <= (1 << 255) - 1
        u256 = (1 << 256) + value if value < 0 else value
        assert 0 <= u256 < (1 << 256)
        self.trace.append(TraceDmemStore(addr, u256, True))

    def load_i32(self, addr: int) -> int:
        '''Read a 32-bit value from memory.

        addr should be 4-byte aligned. The result is returned as a signed
        32-bit integer (appropriate for storing in a riscvmodel Register)

        '''
        assert 0 == addr % 4
        assert addr < 32 * len(self.data)

        idx32 = addr // 4
        idxW = idx32 // 8
        offW = idx32 % 8

        uword = self.data[idxW]
        # Extract the right 32-bit unsigned value
        u32 = (uword >> 8 * offW) & ((1 << 32) - 1)
        # Now convert back to signed and return
        return u32 - (1 << 32) if u32 >> 31 else u32

    def store_i32(self, addr: int, value: int) -> None:
        '''Store a 32-bit signed value to memory.

        addr should be 4-byte aligned.

        '''
        assert 0 == addr % 4
        assert addr < 32 * len(self.data)
        assert -(1 << 31) <= value <= (1 << 31) - 1
        u32 = (1 << 32) + value if value < 0 else value
        assert 0 <= u32 < (1 << 32)
        self.trace.append(TraceDmemStore(addr, u32, False))

    def changes(self) -> List[Trace]:
        return self.trace

    def _commit_store(self, item: TraceDmemStore) -> None:
        if item.is_wide:
            assert 0 <= item.value < (1 << 256)
            self.data[item.addr // 32] = item.value
            return

        idx32 = item.addr // 4
        idxW = idx32 // 8
        offW = idx32 % 8

        # Since we store data in wide form, we have to do a read/modify/write
        # to update. Grab the old word and expand it to a list of 8 u32s.
        u32s = self._get_u32s(idxW)

        # Replace the word we're setting
        assert 0 <= item.value <= (1 << 32) - 1
        u32s[offW] = item.value

        # And write back
        self._set_u32s(idxW, u32s)

    def commit(self) -> None:
        for item in self.trace:
            self._commit_store(item)
        self.trace = []
