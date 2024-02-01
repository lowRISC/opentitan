# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
from typing import Dict, List, Sequence, Optional

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
        dmem_size = get_memory_layout().dmem_size_bytes

        # Check the arguments look sensible, to avoid allocating massive chunks
        # of memory. We know we won't have more than 1 MiB of DMEM.
        if dmem_size > 1024 * 1024:
            raise RuntimeError('Implausibly large DMEM size: {}'
                               .format(dmem_size))

        # The native width for the OTBN wide side is 256 bits. This means that
        # dmem_size needs to be divisible by 32.
        if dmem_size % 32:
            raise RuntimeError('DMEM size ({}) is not divisible by 32.'
                               .format(dmem_size))

        # We represent the contents of DMEM as a list of 32-bit words (unlike
        # the RTL, which uses a 256-bit array). An entry in self.data is None
        # if the word has invalid integrity bits and we'll get an error if we
        # try to read it. Otherwise, we store the integer value.
        num_words = dmem_size // 4
        self.data = [None] * num_words  # type: List[Optional[int]]

        # Because it's an actual memory, stores to DMEM take two cycles in the
        # RTL. We wouldn't need to model this except that a DMEM invalidation
        # (used by the testbench to model integrity errors) shouldn't trash
        # pending writes. We do things in two steps: firstly, we do the
        # trace/commit dance that all the other blocks do. A memory write will
        # generate a trace entry which will appear in changes() at the end of
        # this cycle. However, the first commit() will then move it to the
        # self.pending list. Entries here will only make it to self.data on the
        # next commit().
        self.trace = []  # type: List[TraceDmemStore]
        self.pending = {}  # type: Dict[int, int]

    def _load_5byte_le_words(self, data: bytes) -> None:
        '''Replace the start of memory with data

        The bytes loaded should represent each 32-bit word with 5 bytes,
        consisting of a validity byte (0 or 1) followed by 4 bytes for the word
        itself.

        '''
        if len(data) % 5:
            raise ValueError('Trying to load {} bytes of data, '
                             'which is not a multiple of 5.'
                             .format(len(data)))

        len_data_32 = len(data) // 5
        len_mem_32 = (256 // 32) * len(self.data)

        if len_data_32 > len_mem_32:
            raise ValueError('Trying to load {} bytes of data, but DMEM '
                             'is only {} bytes long.'
                             .format(4 * len_data_32, 32 * len(self.data)))

        # Zero-pad up to the next 32-bit word, represented by 5 bytes. Because
        # things are little-endian, this is like zero-extending the last word.
        if len(data) % 5:
            data = data + b'0' * (5 - (len(data) % 5))

        for idx32, (vld, u32) in enumerate(struct.iter_unpack('<BI', data)):
            if vld not in [0, 1]:
                raise ValueError('The validity byte for 32-bit word {} '
                                 'in the input data is {}, not 0 or 1.'
                                 .format(idx32, vld))
            self.data[idx32] = u32 if vld else None

    def _load_4byte_le_words(self, data: bytes) -> None:
        '''Replace the start of memory with data

        The bytes loaded should represent each 32-bit word with 4 bytes in
        little-endian format.

        '''
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

    def load_le_words(self, data: bytes, has_validity: bool) -> None:
        '''Replace the start of memory with data

        Uses the 5-byte format if has_validity is true and the 4-byte format
        otherwise.

        '''
        if has_validity:
            self._load_5byte_le_words(data)
        else:
            self._load_4byte_le_words(data)

    def dump_le_words(self) -> bytes:
        '''Return the contents of memory as bytes.

        The bytes are formatted as little-endian 32-bit words. These
        words are themselves packed little-endian into 256-bit words.

        '''
        ret = b''
        for idx, u32 in enumerate(self.data):
            # If there's a pending store, apply it. This matches the RTL, where
            # we only observe the memory after that store has landed.
            u32 = self.pending.get(idx, u32)

            if u32 is None:
                ret += struct.pack('<BI', 0, 0)
            else:
                ret += struct.pack('<BI', 1, u32)

        return ret

    def is_valid_256b_addr(self, addr: int) -> bool:
        '''Return true if this is a valid address for a BN.LID/BN.SID'''
        assert addr >= 0
        if addr & 31:
            return False

        word_addr = addr // 4
        if word_addr >= len(self.data):
            return False

        return True

    def load_u256(self, addr: int) -> Optional[int]:
        '''Read a u256 little-endian value from an aligned address'''
        assert addr >= 0
        assert self.is_valid_256b_addr(addr)
        ret_data = 0
        for i in range(256 // 32):
            rd_data = self.load_u32(addr + 4 * i)
            if rd_data is None:
                return None
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

        if (addr + 3) // 4 >= len(self.data):
            return False

        return True

    def load_u32(self, addr: int) -> Optional[int]:
        '''Read a 32-bit value from memory.

        addr should be 4-byte aligned. The result is returned as an unsigned
        32-bit integer.

        '''
        assert addr >= 0
        assert self.is_valid_32b_addr(addr)

        idx = addr // 4

        # Handle "read under write" hazards properly
        pending_val = self.pending.get(idx)
        if pending_val is not None:
            return pending_val

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

    def _commit_trace_entry(self, item: TraceDmemStore) -> None:
        '''Apply a trace entry to self.pending'''
        if item.is_wide:
            assert 0 <= item.value < (1 << 256)
            mask = (1 << 32) - 1
            for i in range(256 // 32):
                wr_data = (item.value >> (i * 32)) & mask
                self.pending[(item.addr // 4) + i] = wr_data

        else:
            assert 0 <= item.value <= (1 << 32) - 1
            self.pending[item.addr // 4] = item.value

    def commit(self) -> None:
        # Move items from self.pending to self.data
        for idx, value in self.pending.items():
            self.data[idx] = value
        self.pending = {}

        # Apply trace entries to self.pending
        for item in self.trace:
            self._commit_trace_entry(item)
        self.trace = []

    def abort(self) -> None:
        self.trace = []

    def empty_dmem(self) -> None:
        self.data = [None] * len(self.data)
