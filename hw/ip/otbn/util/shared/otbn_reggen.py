# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A wrapper around reggen for otbn.hjson'''

import os
import sys
from typing import Optional, Tuple


# We use reggen to read the hjson file. Since that lives somewhere completely
# different from this script (and there aren't __init__.py files scattered all
# over the OpenTitan repository), we have to do sys.path hacks to find it.
_OLD_SYS_PATH = sys.path
try:
    _UTIL_PATH = os.path.join(os.path.dirname(__file__),
                              '..', '..', '..', '..', '..', 'util')
    sys.path = [_UTIL_PATH] + _OLD_SYS_PATH
    import reggen.field  # type: ignore
    import reggen.ip_block   # type: ignore
    import reggen.reg_block   # type: ignore
    import reggen.register  # type: ignore
    import reggen.window  # type: ignore
finally:
    sys.path = _OLD_SYS_PATH

# Re-export some reggen types so that code importing otbn_reggen can get them
# transitively without having to mess around with sys.path.
Register = reggen.register.Register
Field = reggen.field.Field
Window = reggen.window.Window
RegBlock = reggen.reg_block.RegBlock
IpBlock = reggen.ip_block.IpBlock

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
        obj = IpBlock.from_path(path, [])
    except ValueError as err:
        raise RuntimeError('Failed to parse {!r}: {}'.format(path, err))

    reg_bit_width = obj.regwidth
    assert isinstance(reg_bit_width, int) and reg_bit_width >= 0
    reg_byte_width = (reg_bit_width + 7) // 8

    registers = obj.reg_blocks[None]
    assert isinstance(registers, RegBlock)
    _LR_RETVAL = (reg_byte_width, registers)
    return _LR_RETVAL
