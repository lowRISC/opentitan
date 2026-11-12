# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Sequence
from .trace import Trace


class ISPRChange(Trace):
    '''Creates a Trace for each change in an ISPR'''
    def __init__(self, ispr_name: str, width: int, new_value: Optional[int]):
        self.ispr_name = ispr_name
        self.new_value = new_value
        self.width = width

    def trace(self) -> str:
        return '{} = {}'.format(self.ispr_name,
                                Trace.hex_value(self.new_value, self.width))

    def rtl_trace(self) -> str:
        return '> {}: {}'.format(self.ispr_name,
                                 Trace.hex_value(self.new_value, self.width))


class ISPR:
    '''Models a Internal Special Purpose Register'''
    def __init__(self, name: str, width: int):
        self.name = name
        self.width = width
        self._pending_write = False

    def has_value(self) -> bool:
        '''Return whether the ISPR has a valid value'''
        return True

    def on_start(self) -> None:
        '''Reset the ISPR if necessary for the start of an operation'''
        return

    def read_unsigned(self) -> int:
        '''Get the stored value as an unsigned integer of self.width bits.'''
        raise NotImplementedError()

    def write_unsigned(self, value: int) -> None:
        '''Set the stored value as an unsigned integer of self.width bits.'''
        raise NotImplementedError()

    def read_signed(self) -> int:
        '''Get the stored value as a signed integer of self.width bits.'''
        uval = self.read_unsigned()
        return uval - (1 << self.width if uval >> (self.width - 1) else 0)

    def write_signed(self, value: int) -> None:
        '''Set the stored value as a signed integer of self.width bits.'''
        assert -(1 << (self.width)) <= value < (1 << (self.width - 1))
        uval = (1 << self.width) + value if value < 0 else value
        self.write_unsigned(uval)

    def commit(self) -> None:
        '''Commit pending changes'''
        self._pending_write = False

    def abort(self) -> None:
        '''Abort pending changes'''
        self._pending_write = False

    def changes(self) -> Sequence[Trace]:
        '''Return list of pending architectural changes'''
        return []


class DumbISPR(ISPR):
    '''Models a ISPR without special behaviour'''
    def __init__(self, name: str, width: int):
        super().__init__(name, width)
        self.on_start()

    def on_start(self) -> None:
        self._value = 0
        self._next_value: Optional[int] = None

    def read_unsigned(self) -> int:
        return self._value

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)
        self._next_value = value
        self._pending_write = True

    def write_invalid(self) -> None:
        self._next_value = None
        self._pending_write = True

    def commit(self) -> None:
        if self._next_value is not None:
            self._value = self._next_value
        self._next_value = None
        self._pending_write = False

    def abort(self) -> None:
        self._next_value = None
        self._pending_write = False

    def changes(self) -> List[ISPRChange]:
        return ([ISPRChange(self.name, self.width, self._next_value)]
                if self._pending_write else [])


class CtrlCSR(ISPR):
    '''Models a control CSR where bits are used to issue a command.

    Control CSRs only issue commands and always read as 0.
    '''

    # Define here the valid command bits.
    CMD_MASK = 0x00

    def __init__(self, name: str):
        super().__init__(name, 32)
        self.on_start()

    def on_start(self) -> None:
        self._cmd = 0
        self._cmd_next: Optional[int] = None
        # Full 32-bit value of a SW write, required for tracing.
        self._write_value = 0
        self._pending_write = False

    def read_unsigned(self) -> int:
        # Cmd bits always read back as 0.
        return 0

    def write_unsigned(self, value: int) -> None:
        # Keep the full written value for tracing.
        self._write_value = value & ((1 << self.width) - 1)
        self._cmd_next = value & self.CMD_MASK
        self._pending_write = True

    def take_cmd(self) -> int:
        '''Read and clear the current command. Must be called before the next insn executes.'''
        cmd = self._cmd
        self._cmd = 0
        return cmd

    def peek_pending_cmd(self) -> int:
        '''Return the command staged by the current insn (0 if none). To be used after the current
        insn executed.'''
        return self._cmd_next if self._cmd_next is not None else 0

    def wipe(self) -> None:
        self._cmd = 0
        self._cmd_next = None
        self._write_value = 0
        self._pending_write = False

    def commit(self) -> None:
        if self._cmd_next is not None:
            self._cmd = self._cmd_next
            self._cmd_next = None
        self._pending_write = False

    def abort(self) -> None:
        self._cmd_next = None
        self._pending_write = False

    def changes(self) -> List[ISPRChange]:
        if self._pending_write:
            return [ISPRChange(self.name, self.width, self._write_value)]
        return []
