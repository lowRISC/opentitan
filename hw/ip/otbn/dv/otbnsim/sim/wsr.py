# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional

from .trace import Trace


class TraceWSR(Trace):
    def __init__(self, wsr_name: str, new_value: int):
        self.wsr_name = wsr_name
        self.new_value = new_value

    def trace(self) -> str:
        return '{} = {:#x}'.format(self.wsr_name, self.new_value)

    def rtl_trace(self) -> str:
        return '> {}: {}'.format(self.wsr_name,
                                 Trace.hex_value(self.new_value, 256))


class WSR:
    '''Models a Wide Status Register'''
    def __init__(self, name: str):
        self.name = name

    def read_unsigned(self) -> int:
        '''Get the stored value as a 256-bit unsigned value'''
        raise NotImplementedError()

    def write_unsigned(self, value: int) -> None:
        '''Set the stored value as a 256-bit unsigned value'''
        raise NotImplementedError()

    def read_signed(self) -> int:
        '''Get the stored value as a 256-bit signed value'''
        uval = self.read_unsigned()
        return uval - (1 << 256 if uval >> 255 else 0)

    def write_signed(self, value: int) -> None:
        '''Set the stored value as a 256-bit signed value'''
        assert -(1 << 255) <= value < (1 << 255)
        uval = (1 << 256) + value if value < 0 else value
        self.write_unsigned(uval)

    def commit(self) -> None:
        '''Commit pending changes'''
        return

    def abort(self) -> None:
        '''Abort pending changes'''
        return

    def changes(self) -> List[TraceWSR]:
        '''Return list of pending architectural changes'''
        return []


class DumbWSR(WSR):
    '''Models a WSR without special behaviour'''
    def __init__(self, name: str):
        super().__init__(name)
        self._value = 0
        self._next_value = None  # type: Optional[int]

    def read_unsigned(self) -> int:
        return self._value

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << 256)
        self._next_value = value

    def commit(self) -> None:
        if self._next_value is not None:
            self._value = self._next_value
        self._next_value = None

    def abort(self) -> None:
        self._next_value = None

    def changes(self) -> List[TraceWSR]:
        return ([TraceWSR(self.name, self._next_value)]
                if self._next_value is not None
                else [])


class RandWSR(WSR):
    '''The magic RND WSR'''
    def __init__(self, name: str):
        super().__init__(name)

        # For now, the RTL doesn't have a real "random number generator".
        # Eventually, it will have an LFSR of some sort, seeded by the
        # CSRNG/EDN. We'll model that properly when we've specced it out. Until
        # then, random numbers are constant.  This constant must match the one
        # in the RTL (the `rnd` signal in the `otbn_core` module found in
        # rtl/otbn_core.sv). If changed here it must be changed there to match.
        # Constant for RND is the binary bit pattern 1001 (0x9 hex) repeated to
        # fill a 256-bit word.
        u32 = 0x99999999
        u64 = (u32 << 32) | u32
        u128 = (u64 << 64) | u64
        self._random_value = (u128 << 128) | u128

    def read_unsigned(self) -> int:
        return self._random_value

    def read_u32(self) -> int:
        '''Read a 32-bit unsigned result'''
        return self._random_value & ((1 << 32) - 1)

    def write_unsigned(self, value: int) -> None:
        return


class WSRFile:
    '''A model of the WSR file'''
    def __init__(self) -> None:
        self.MOD = DumbWSR('MOD')
        self.RND = RandWSR('RND')
        self.ACC = DumbWSR('ACC')

    def _wsr_for_idx(self, idx: int) -> WSR:
        assert 0 <= idx <= 2
        return {
            0: self.MOD,
            1: self.RND,
            2: self.ACC
        }[idx]

    def read_at_idx(self, idx: int) -> int:
        '''Read the WSR at idx as an unsigned 256-bit value'''
        return self._wsr_for_idx(idx).read_unsigned()

    def write_at_idx(self, idx: int, value: int) -> None:
        '''Write the WSR at idx as an unsigned 256-bit value'''
        return self._wsr_for_idx(idx).write_unsigned(value)

    def commit(self) -> None:
        self.MOD.commit()
        self.RND.commit()
        self.ACC.commit()

    def abort(self) -> None:
        self.MOD.abort()
        self.RND.abort()
        self.ACC.abort()

    def changes(self) -> List[TraceWSR]:
        return self.MOD.changes() + self.RND.changes() + self.ACC.changes()
