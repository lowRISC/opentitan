# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

# A copy of the list of error codes. This also appears in the documentation and
# otbn_pkg.sv: we should probably be generating them from the hjson every time.
ERR_CODE_NO_ERROR = 0
ERR_CODE_BAD_DATA_ADDR = 1 << 0
ERR_CODE_BAD_INSN_ADDR = 1 << 1
ERR_CODE_CALL_STACK = 1 << 2
ERR_CODE_ILLEGAL_INSN = 1 << 3
ERR_CODE_LOOP = 1 << 4
ERR_CODE_FATAL_IMEM = 1 << 5
ERR_CODE_FATAL_DMEM = 1 << 6
ERR_CODE_FATAL_REG = 1 << 7


class Alert(Exception):
    '''An exception raised to signal that the program did something wrong

    This maps onto alerts in the implementation. The err_code value is the
    value that should be written to the ERR_CODE external register.

    '''
    # Subclasses should override this class field or the error_code method
    err_code = None  # type: Optional[int]

    def error_code(self) -> int:
        assert self.err_code is not None
        return self.err_code


class BadAddrError(Alert):
    '''Raised when loading or storing or setting PC with a bad address'''

    def __init__(self, operation: str, addr: int, what: str):
        assert operation in ['pc',
                             'narrow load', 'narrow store',
                             'wide load', 'wide store']
        self.operation = operation
        self.addr = addr
        self.what = what

    def error_code(self) -> int:
        return (ERR_CODE_BAD_INSN_ADDR
                if self.operation == 'fetch'
                else ERR_CODE_BAD_DATA_ADDR)

    def __str__(self) -> str:
        return ('Bad {} address of {:#08x}: {}.'
                .format(self.operation, self.addr, self.what))


class LoopError(Alert):
    '''Raised when doing something wrong with a LOOP/LOOPI'''

    err_code = ERR_CODE_LOOP

    def __init__(self, what: str):
        self.what = what

    def __str__(self) -> str:
        return 'Loop error: {}'.format(self.what)
