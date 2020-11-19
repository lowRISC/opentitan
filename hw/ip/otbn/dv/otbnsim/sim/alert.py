# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

# A copy of the list of error codes. This also appears in otbn.hjson and
# otbn_pkg.sv: we should probably be generating them from the hjson every time.
ERR_CODE_NO_ERROR = 0
ERR_CODE_BAD_DATA_ADDR = 1
ERR_CODE_CALL_STACK = 2


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
