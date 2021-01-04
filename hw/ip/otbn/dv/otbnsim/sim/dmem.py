# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
from typing import List, Sequence

from shared.mem_layout import get_memory_layout

from .alert import BadAddrError
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

        num_words = dmem_size // 32

        # Initialise the memory to an arbitrary "bad" constant (here,
        # 0xdeadbeef). We could initialise to a random value, but maybe it's
        # more helpful to generate something recognisable for now.
        uninit = 0
        for i in range(32 // 4):
            uninit = (uninit << 32) | 0xdeadbeef

        self.data = [uninit] * num_words
        self.trace = []  # type: List[TraceDmemStore]

    def _get_u32s(self, idx: int) -> List[int]:
        '''Return the value at idx as 8 uint32's

        These are ordered by increasing address, so the first word from
        _get_u32s(0) will correspond to bytes at addresses 0x0 through 0x3.

        These uint32's are the words that get loaded by word accesses to
        memory. Since these accesses are also little-endian, the byte at memory
        address 0x0 (which holds the LSB for the first 256-bit value) will also
        be the LSB of the first u32 returned by _get_u32s(0).

        '''
        assert 0 <= idx < len(self.data)

        word = self.data[idx]
        assert 0 <= word <= 1 << 256

        # Pack this unsigned word into w32s as 8 32-bit numbers. Note that
        # this packing is "little-endian": the first unsigned word contains
        # the LSB of the value.
        ret = []
        w32_mask = (1 << 32) - 1
        for subidx in range(8):
            ret.append((word >> (32 * subidx)) & w32_mask)

        return ret

    def _set_u32s(self, idx: int, u32s: List[int]) -> None:
        '''Set the value at idx with 8 uint32's in little-endian order'''
        assert 0 <= idx < len(self.data)
        assert len(u32s) == 8

        # Accumulate the u32s into a 256-bit unsigned number (in a
        # little-endian fashion)
        u256 = 0
        for u32 in reversed(u32s):
            assert 0 <= u32 <= (1 << 32) - 1
            u256 = (u256 << 32) | u32

        # Store it!
        self.data[idx] = u256

    def load_le_words(self, data: bytes) -> None:
        '''Replace the start of memory with data'''
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
        u32s = []  # type: List[int]
        for idx in range(len(self.data)):
            u32s += self._get_u32s(idx)
        return struct.pack('<{}I'.format(len(u32s)), *u32s)

    def load_u256(self, addr: int) -> int:
        '''Read a u256 little-endian value from an aligned address'''
        assert addr >= 0

        if addr & 31:
            raise BadAddrError('wide load', addr,
                               'address is not 32-byte aligned')

        word_addr = addr // 32

        if word_addr >= len(self.data):
            raise BadAddrError('wide load', addr,
                               'address is above the top of dmem')

        return self.data[word_addr]

    def store_u256(self, addr: int, value: int) -> None:
        '''Write a u256 little-endian value to an aligned address'''
        assert addr >= 0
        assert 0 <= value < (1 << 256)

        if addr & 31:
            raise BadAddrError('wide store', addr,
                               'address is not 32-byte aligned')

        word_addr = addr // 32
        if word_addr >= len(self.data):
            raise BadAddrError('wide store', addr,
                               'address is above the top of dmem')

        self.trace.append(TraceDmemStore(addr, value, True))

    def load_u32(self, addr: int) -> int:
        '''Read a 32-bit value from memory.

        addr should be 4-byte aligned. The result is returned as an unsigned
        32-bit integer.

        '''
        assert addr >= 0
        if addr & 3:
            raise BadAddrError('narrow load', addr,
                               'address is not 4-byte aligned')
        if (addr + 3) // 32 >= len(self.data):
            raise BadAddrError('narrow load', addr,
                               'address is above the top of dmem')

        idx32 = addr // 4
        idxW = idx32 // 8
        offW = idx32 % 8

        return self._get_u32s(idxW)[offW]

    def store_u32(self, addr: int, value: int) -> None:
        '''Store a 32-bit unsigned value to memory.

        addr should be 4-byte aligned.

        '''
        assert addr >= 0
        assert 0 <= value <= (1 << 32) - 1

        if addr & 3:
            raise BadAddrError('narrow load', addr,
                               'address is not 4-byte aligned')
        if (addr + 3) // 32 >= len(self.data):
            raise BadAddrError('narrow load', addr,
                               'address is above the top of dmem')

        self.trace.append(TraceDmemStore(addr, value, False))

    def changes(self) -> Sequence[Trace]:
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

    def abort(self) -> None:
        self.trace = []
