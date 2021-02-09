# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A wrapper around reggen for otbn.hjson'''

import os
import sys
from typing import List, Optional, Tuple

import hjson  # type: ignore


# We use reggen to read the hjson file. Since that lives somewhere completely
# different from this script (and there aren't __init__.py files scattered all
# over the OpenTitan repository), we have to do sys.path hacks to find it.
_OLD_SYS_PATH = sys.path
try:
    _UTIL_PATH = os.path.join(os.path.dirname(__file__),
                              '..', '..', '..', '..', '..', 'util')
    sys.path = [_UTIL_PATH] + _OLD_SYS_PATH
    from reggen.validate import checking_dict, validate   # type: ignore
    import reggen.field  # type: ignore
    import reggen.register  # type: ignore
    import reggen.window  # type: ignore
finally:
    sys.path = _OLD_SYS_PATH

# Re-export some reggen types so that code importing otbn_reggen can get them
# transitively without having to mess around with sys.path.
Register = reggen.register.Register
Field = reggen.field.Field
Window = reggen.window.Window

_LR_RETVAL = None  # type: Optional[Tuple[int, List[object]]]


def load_registers() -> Tuple[int, List[object]]:
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
        with open(path, 'r') as handle:
            obj = hjson.loads(handle.read(),
                              use_decimal=True,
                              object_pairs_hook=checking_dict)
    except ValueError as err:
        raise RuntimeError('Failed to parse {!r}: {}'.format(path, err))

    # Unconditionally run second validation pass
    num_errs = validate(obj)
    if num_errs:
        raise RuntimeError('Reggen second validation pass failed for {!r} '
                           '({} errors).'
                           .format(path, num_errs))

    reg_bit_width = int(obj.get('regwidth', 32))
    assert isinstance(reg_bit_width, int) and reg_bit_width >= 0
    reg_byte_width = reg_bit_width // 8

    # obj should be an OrderedDict and should contain a registers entry
    # (checked by validate). This is a list of registers which we'll return.
    # The validation code would also have exploded if it wasn't a list of
    # dictionaries, so we can assert the type safely.
    registers = obj['registers']
    assert isinstance(registers, list)
    _LR_RETVAL = (reg_byte_width, registers)
    return _LR_RETVAL
