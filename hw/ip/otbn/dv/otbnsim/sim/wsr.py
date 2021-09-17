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
    '''The magic RND WSR

    RND is special as OTBN can stall on reads to it. A read from RND either
    immediately returns data from a cache of a previous EDN request (triggered
    by writing to the RND_PREFETCH CSR) or waits for data from the EDN. To model
    this anything reading from RND must first call `request_value` which returns
    True if the value is available.
    '''
    def __init__(self, name: str):
        super().__init__(name)

        self._random_value = None  # type: Optional[int]
        self._random_value_read = False
        self.pending_request = False

    def read_unsigned(self) -> int:
        assert self._random_value is not None

        self._random_value_read = True

        return self._random_value

    def read_u32(self) -> int:
        '''Read a 32-bit unsigned result'''
        return self.read_unsigned() & ((1 << 32) - 1)

    def write_unsigned(self, value: int) -> None:
        '''Writes to RND are ignored

        Note this is different to `set_unsigned`. This is used by executing
        instruction, see `set_unsigned` docstring for more details
        '''
        return

    def commit(self) -> None:
        if self._random_value_read:
            self._random_value = None
            self.pending_request = False

        self._random_value_read = False

    def request_value(self) -> bool:
        '''Signals intent to read RND, returns True if a value is available'''
        if self._random_value is not None:
            return True

        self.pending_request = True
        return False

    def set_unsigned(self, value: int) -> None:
        '''Sets a random value that can be read by a future `read_unsigned`

        This is different to `write_unsigned`, that is used by an executing
        instruction to write to RND. This is used by the simulation environment
        to provide a value that is later read by `read_unsigned` and doesn't
        relate to instruction execution (e.g. in an RTL simulation it monitors
        the EDN bus and supplies the simulator with an RND value when a fresh
        one is seen on the EDN bus).
        '''
        assert 0 <= value < (1 << 256)
        self._random_value = value


class WSRFile:
    '''A model of the WSR file'''
    def __init__(self) -> None:
        self.MOD = DumbWSR('MOD')
        self.RND = RandWSR('RND')
        self.ACC = DumbWSR('ACC')

        self._by_idx = {
            0: self.MOD,
            1: self.RND,
            # TODO: Implement 2: URND
            3: self.ACC
        }

    def check_idx(self, idx: int) -> bool:
        '''Return True if idx is a valid WSR index'''
        return idx in self._by_idx

    def read_at_idx(self, idx: int) -> int:
        '''Read the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        return self._by_idx[idx].read_unsigned()

    def write_at_idx(self, idx: int, value: int) -> None:
        '''Write the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        return self._by_idx[idx].write_unsigned(value)

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
