# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from .constants import ErrBits
from .reg import Reg, RegFile


class CallStackReg(Reg):
    '''A register used to represent x1'''

    # The depth of the x1 call stack
    stack_depth = 8

    def __init__(self, parent: 'GPRs'):
        super().__init__(parent, 1, 32, 0)
        self.stack = []  # type: List[int]
        self.saw_read = False
        self.gpr_parent = parent

    # We overload read_unsigned here, to handle the read-sensitive behaviour
    # without needing the base class to deal with it.
    def read_unsigned(self, backdoor: bool = False) -> int:
        if backdoor:
            # If a backdoor access, don't take note of the read. If the stack
            # turns out to be empty, return some "obviously bogus" value.
            return self.stack[-1] if self.stack else 0xcafef00d

        if not self.stack:
            self.gpr_parent.call_stack_err = True
            return 0

        # Mark that we've read something (so that we pop from the stack as part
        # of commit) and return the top of the stack.
        self.saw_read = True
        return self.stack[-1]

    def post_insn(self) -> None:
        if self._next_uval is not None:
            if not self.saw_read and len(self.stack) == 8:
                self.gpr_parent.call_stack_err = True

    def commit(self) -> None:
        if self.saw_read:
            assert self.stack
            self.stack.pop()
            self.saw_read = False

        if self._next_uval is not None:
            # We should already have checked that we won't overflow the call
            # stack in post_insn().
            assert len(self.stack) <= 8
            self.stack.append(self._next_uval)

        super().commit()

    def abort(self) -> None:
        self.saw_read = False
        super().abort()

    def start(self) -> None:
        '''Executed on start of operation.'''
        self.stack = []
        self.saw_read = False


class GPRs(RegFile):
    '''The narrow OTBN register file'''

    def __init__(self) -> None:
        super().__init__('x', 32, 32)
        self._x1 = CallStackReg(self)
        self.call_stack_err = False

    def get_reg(self, idx: int) -> Reg:
        if idx == 0:
            # If idx == 0, this is a zeros register that should ignore writes.
            # Return a fresh Reg with no parent, so writes to it have no
            # effect.
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

    def post_insn(self) -> None:
        return self._x1.post_insn()

    def err_bits(self) -> int:
        return ErrBits.CALL_STACK if self.call_stack_err else 0

    def commit(self) -> None:
        super().commit()
        assert not self.call_stack_err
        self._x1.commit()

    def abort(self) -> None:
        super().abort()
        self._x1.abort()
        self.call_stack_err = False

    def empty_call_stack(self) -> None:
        '''Clear call stack.'''
        self._x1.start()

    def wipe(self) -> None:
        '''Wipe all registers to zero and clear the call stack'''
        self._x1.start()
        for idx in range(2, 32):
            self.get_reg(idx).write_invalid()
