# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A wrapper around reggen for otbn.hjson'''

import os
from typing import Optional, Tuple

from reggen import ip_block, reg_block

_LR_RETVAL = None  # type: Optional[Tuple[int, object]]


def load_registers() -> Tuple[int, object]:
    '''Load otbn.hjson with reggen

    Returns (width, regs) where width is the register width and regs is a
    list of Register, MultiRegister or Window objects. Memoized.

    '''
    global _LR_RETVAL
    if _LR_RETVAL is not None:
        return _LR_RETVAL

    path = os.path.join(os.path.dirname(__file__),
                        '..', '..', 'data', 'otbn.hjson')

    try:
        obj = ip_block.IpBlock.from_path(path, [])
    except ValueError as err:
        raise RuntimeError('Failed to parse {!r}: {}'.format(path, err))

    reg_bit_width = obj.regwidth
    assert isinstance(reg_bit_width, int) and reg_bit_width >= 0
    reg_byte_width = (reg_bit_width + 7) // 8

    registers = obj.reg_blocks[None]
    assert isinstance(registers, reg_block.RegBlock)
    _LR_RETVAL = (reg_byte_width, registers)
    return _LR_RETVAL
