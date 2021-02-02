# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

# A copy of the list of bits in the ERR_BITS register. This also appears in the
# documentation and otbn_pkg.sv: we should probably be generating them from the
# hjson every time.
BAD_DATA_ADDR = 1 << 0
BAD_INSN_ADDR = 1 << 1
CALL_STACK = 1 << 2
ILLEGAL_INSN = 1 << 3
LOOP = 1 << 4
FATAL_IMEM = 1 << 5
FATAL_DMEM = 1 << 6
FATAL_REG = 1 << 7


class Alert:
    '''An object describing something the program did wrong

    This maps onto alerts in the implementation. The err_bit value is the
    value that should be OR'd into the ERR_BITS external register.

    '''
    # Subclasses should override this class field or the error_bit method
    err_bit = None  # type: Optional[int]

    def error_bit(self) -> int:
        assert self.err_bit is not None
        return self.err_bit


class BadAddrError(Alert):
    '''Generated when loading or storing or setting PC with a bad address'''

    def __init__(self, operation: str, addr: int, what: str):
        assert operation in ['pc',
                             'narrow load', 'narrow store',
                             'wide load', 'wide store']
        self.operation = operation
        self.addr = addr
        self.what = what

    def error_bit(self) -> int:
        return BAD_INSN_ADDR if self.operation == 'fetch' else BAD_DATA_ADDR

    def __str__(self) -> str:
        return ('Bad {} address of {:#08x}: {}.'
                .format(self.operation, self.addr, self.what))


class LoopError(Alert):
    '''Generated when doing something wrong with a LOOP/LOOPI'''

    err_bit = LOOP

    def __init__(self, what: str):
        self.what = what

    def __str__(self) -> str:
        return 'Loop error: {}'.format(self.what)


class IllegalInsnError(Alert):
    '''Generated on a bad instruction'''
    err_bit = ILLEGAL_INSN

    def __init__(self, word: int, msg: str):
        self.word = word
        self.msg = msg

    def __str__(self) -> str:
        return ('Illegal instruction {:#010x}: {}'.format(self.word, self.msg))


class CallStackError(Alert):
    '''Raised when under- or over-flowing the call stack'''

    err_bit = CALL_STACK

    def __init__(self, is_overflow: bool):
        self.is_overflow = is_overflow

    def __str__(self) -> str:
        xflow = 'overflow' if self.is_overflow else 'underflow'
        return 'Instruction caused {} of x1 call stack.'.format(xflow)
