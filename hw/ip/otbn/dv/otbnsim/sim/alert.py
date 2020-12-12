# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

# A copy of the list of error codes. This also appears in the documentation and
# otbn_pkg.sv: we should probably be generating them from the hjson every time.
ERR_CODE_NO_ERROR = 0x0
ERR_CODE_BAD_DATA_ADDR = 0x1
ERR_CODE_BAD_INSN_ADDR = 0x2
ERR_CODE_CALL_STACK = 0x3
ERR_CODE_ILLEGAL_INSN = 0x4
ERR_CODE_LOOP = 0x5
ERR_CODE_FATAL_IMEM = 0x80
ERR_CODE_FATAL_DMEM = 0x81
ERR_CODE_FATAL_REG = 0x82


class Alert(Exception):
    '''An exception raised to signal that the program did something wrong

    This maps onto alerts in the implementation. The err_code value is the
    value that should be written to the ERR_CODE external register.

    '''
    # Subclasses should override this class field
    err_code = None  # type: Optional[int]

    def error_code(self) -> int:
        assert self.err_code is not None
        return self.err_code


class LoopError(Alert):
    '''Raised when doing something wrong with a LOOP/LOOPI'''

    err_code = ERR_CODE_LOOP

    def __init__(self, what: str):
        self.what = what

    def __str__(self) -> str:
        return 'Loop error: {}'.format(self.what)
