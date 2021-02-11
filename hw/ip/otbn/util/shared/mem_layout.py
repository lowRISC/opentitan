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

from typing import Dict, Optional, Tuple

from .otbn_reggen import load_registers, RegBlock

# A window is represented as (offset, size)
_Window = Tuple[int, int]


def extract_windows(reg_byte_width: int, regs: object) -> Dict[str, _Window]:
    '''Make sense of the list of register definitions and extract memories'''

    windows = {}

    assert isinstance(regs, RegBlock)
    for entry in regs.windows:
        name = entry.name or 'Window at +{:#x}'.format(entry.offset)

        # Should be guaranteed by RegBlock constructor
        assert name not in windows

        windows[name] = (entry.offset, entry.size_in_bytes)

    return windows


_LAYOUT = None  # type: Optional[Dict[str, Tuple[int, int]]]


def get_memory_layout() -> Dict[str, Tuple[int, int]]:
    '''Read otbn.hjson to get IMEM / DMEM layout

    Returns a dictionary with two entries, keyed 'IMEM' and 'DMEM'. The value
    at each entry is a pair (offset, size_in_bytes).

    '''
    global _LAYOUT
    if _LAYOUT is not None:
        return _LAYOUT

    reg_byte_width, registers = load_registers()
    windows = extract_windows(reg_byte_width, registers)

    xmem_names = {'IMEM', 'DMEM'}
    for name in xmem_names:
        if name not in windows:
            raise RuntimeError("otbn.hjson doesn't have a window called {}."
                               .format(name))
    if len(windows) != 2:
        raise RuntimeError("Unexpected windows in otbn.hjson: {}"
                           .format(list(set(windows.keys()) - xmem_names)))

    _LAYOUT = windows
    return _LAYOUT


if __name__ == '__main__':
    for name, (off, width) in get_memory_layout().items():
        print('{}: {} bytes; LMA {:#x}'.format(name, width, off))
