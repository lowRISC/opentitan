# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from .alert import Alert, ERR_CODE_CALL_STACK
from .reg import Reg, RegFile


class CallStackError(Alert):
    '''Raised when under- or over-flowing the call stack'''

    err_code = ERR_CODE_CALL_STACK

    def __init__(self, is_overflow: bool):
        self.is_overflow = is_overflow

    def __str__(self) -> str:
        xflow = 'overflow' if self.is_overflow else 'underflow'
        return 'Instruction caused {} of x1 call stack.'.format(xflow)


class CallStackReg(Reg):
    '''A register used to represent x1'''

    # The depth of the x1 call stack
    stack_depth = 8

    def __init__(self, parent: RegFile):
        super().__init__(parent, 1, 32, 0)
        self.stack = []  # type: List[int]
        self.saw_read = False

    # We overload read_unsigned here, to handle the read-sensitive behaviour
    # without needing the base class to deal with it.
    def read_unsigned(self, backdoor: bool = False) -> int:
        if backdoor:
            # If a backdoor access, don't take note of the read. If the stack
            # turns out to be empty, return some "obviously bogus" value.
            return self.stack[-1] if self.stack else 0xcafef00d

        if not self.stack:
            raise CallStackError(False)

        # Mark that we've read something (so that we pop from the stack as part
        # of commit) and return the top of the stack.
        self.saw_read = True
        return self.stack[-1]

    def write_unsigned(self, uval: int, backdoor: bool = False) -> None:
        super().write_unsigned(uval, backdoor)

    def commit(self) -> None:
        if self.saw_read:
            assert self.stack
            self.stack.pop()
            self.saw_read = False

        if self._next_uval is not None:
            if len(self.stack) == 8:
                raise CallStackError(True)
            self.stack.append(self._next_uval)

        super().commit()

    def abort(self) -> None:
        self.saw_read = False
        super().abort()


class GPRs(RegFile):
    '''The narrow OTBN register file'''

    def __init__(self) -> None:
        super().__init__('x', 32, 32)
        self._x1 = CallStackReg(self)

    def get_reg(self, idx: int) -> Reg:
        if idx == 0:
            # If idx == 0, this is a zeros register that should ignore writes.
            # Return a fresh Reg with no parent, so writes to it have no effect.
            return Reg(None, 0, 32, 0)
        elif idx == 1:
            # If idx == 1, we return self._x1: element 1 of the underlying
            # register file is not actually used.
            return self._x1
        else:
            return super().get_reg(idx)

    def peek_call_stack(self) -> List[int]:
        '''Get the call stack, bottom-first.'''
        return self._x1.stack

    def commit(self) -> None:
        self._x1.commit()
        super().commit()

    def abort(self) -> None:
        self._x1.abort()
        super().abort()
