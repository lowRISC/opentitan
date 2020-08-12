# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Simple code that understands enough of otbn.hjson to get a memory layout

Each memory will have an associated "window" entry, which has an offset from
the start of the IP block's register space. This offset will be treated as an
LMA for this memory and these memory LMAs will be used uniformly in
OTBN-specific tooling. This avoids the result depending on the address layout
of the wider chip.

In particular, note that OTBN ELF binaries will use these LMAs (the VMAs are in
OTBN's address space, with both IMEM and DMEM starting at 0). A tool that takes
such binaries and incorporates them into a top-level image will need to do
address translation (essentially, just adding the base address of the OTBN IP
block).

'''

import os
import sys
from typing import Dict, List, Mapping, Tuple

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
finally:
    sys.path = _OLD_SYS_PATH


# An hjson dict is actually an OrderedDict, but typing/mypy support for that is
# a little spotty, so we'll use a generic Mapping type.
_HjsonDict = Mapping[str, object]

# A window is represented as (offset, size)
_Window = Tuple[int, int]


def load_registers(path: str) -> Tuple[int, List[_HjsonDict]]:
    '''Load hjson file at path with reggen

    Return its register width and list of registers.

    '''
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
    return (reg_byte_width, registers)


def extract_windows(reg_byte_width: int,
                    registers: List[_HjsonDict]) -> Dict[str, _Window]:
    '''Make sense of the list of register definitions and extract memories'''

    # Conveniently, reggen's validate method stores 'genoffset' (the offset to
    # the start) for each window, so we can just look that up.
    windows = {}

    for reg in registers:
        assert isinstance(reg, dict)
        window = reg.get('window')
        if window is None:
            continue

        assert isinstance(window, dict)

        offset = window['genoffset']
        assert isinstance(offset, int)

        items = int(window['items'])
        window_name = window.get('name', 'Window at +{:#x}'.format(offset))
        assert isinstance(window_name, str)
        if window_name in windows:
            raise ValueError('Duplicate window entry with name {!r}.'
                             .format(window_name))

        windows[window_name] = (offset, items * reg_byte_width)

    return windows


def get_memory_layout() -> Dict[str, Tuple[int, int]]:
    '''Read otbn.hjson to get IMEM / DMEM layout

    Returns a dictionary with two entries, keyed 'IMEM' and 'DMEM'. The value
    at each entry is a pair (offset, size_in_bytes).

    '''
    hjson_path = os.path.join(os.path.dirname(__file__),
                              '..', '..', 'data', 'otbn.hjson')
    reg_byte_width, registers = load_registers(hjson_path)
    windows = extract_windows(reg_byte_width, registers)

    xmem_names = {'IMEM', 'DMEM'}
    for name in xmem_names:
        if name not in windows:
            raise RuntimeError("otbn.hjson doesn't have a window called {}."
                               .format(name))
    if len(windows) != 2:
        raise RuntimeError("Unexpected windows in otbn.hjson: {}"
                           .format(list(set(windows.keys()) - xmem_names)))

    return windows


if __name__ == '__main__':
    for name, (off, width) in get_memory_layout().items():
        print('{}: {} bytes; LMA {:#x}'.format(name, width, off))
