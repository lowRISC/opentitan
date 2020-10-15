# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from .reg import Reg, RegFile


class GPRs(RegFile):
    '''The narrow OTBN register file'''
    def __init__(self) -> None:
        super().__init__('x', 32, 32)

        # The call stack for x1 and its pending updates. self.callstack is
        # never empty and (after commit) the tail always matches
        # self._registers[1].read_unsigned() (pushing from the right)
        self._callstack = [0]  # type: List[int]
        self._callstack_pop = False

    def mark_read(self, idx: int) -> None:
        super().mark_read(idx)
        if idx == 1:
            self._callstack_pop = True

    def get_reg(self, idx: int) -> Reg:
        # If idx == 0, this is a zeros register that should ignore writes.
        # Return a fresh Reg with no parent, so writes to it have no effect.
        if idx == 0:
            return Reg(None, 0, 32, 0)
        return super().get_reg(idx)

    def post_insn(self) -> None:
        '''Update call stack after instruction execution but before commit

        This is not idempotent: call it exactly once.

        '''
        callstack_push = 1 in self._pending_writes

        # If we read from the call stack, we have popped from it. (Even if the
        # stack is empty, we treat this as a logical pop. We need to decide
        # what happens here: see issue #3239).
        if self._callstack_pop:
            if len(self._callstack) > 1:
                self._callstack.pop()

            # Write the new head of the call stack to the relevant register,
            # unless x1 has a pending write (which means that we had an
            # instruction like "addi x1, x1, 0", so the pop happened logically
            # before the push)
            if not callstack_push:
                self._registers[1].write_unsigned(self._callstack[-1])

        # If there is a pending write to x1 (which wasn't caused by the
        # callstack pop code just above) then callstack_push will be true. In
        # that case, we should push the new value onto the call stack.
        if callstack_push:
            new_x1 = self._registers[1].read_next()
            assert new_x1 is not None
            self._callstack.append(new_x1)

    def peek_call_stack(self) -> List[int]:
        '''Get a list of values on the call stack'''
        # _callstack is never empty and always contains 0 as the first element,
        # so strip that off the returned value.
        return self._callstack[1:]

    def commit(self) -> None:
        self._callstack_pop = False
        super().commit()
