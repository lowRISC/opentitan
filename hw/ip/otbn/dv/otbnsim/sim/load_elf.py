# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''OTBN ELF file handling'''

import re
import struct
from typing import Optional, Dict

from shared.elf import read_elf

from .decode import decode_words
from .sim import LoopWarps, OTBNSim


def _get_exp_end_addr(symbols: Dict[str, int]) -> Optional[int]:
    '''Get the expected end address for a run of this binary

    This is the value of the ELF symbol _expected_end_addr. If the symbol
    doesn't exist, returns None.

    '''
    if '_expected_end_addr' in symbols:
        return symbols['_expected_end_addr']
    return None


def _get_loop_warps(symbols: Dict[str, int]) -> LoopWarps:
    '''Return a list of the requested loop warps

    These are read in the format described in sim.py. A warp is specified as a
    symbol of the form

      _loop_warp_FROM_TO

    pointing at the address where it should take effect. If a symbol specifies
    TO < FROM, we raise a RuntimeError. If there are multiple symbols that
    specify warps at a particular address/count pair, we raise a RuntimeError.

    '''
    pat = re.compile(r'_loop_warp_([0-9]+)_([0-9]+)')

    ret = {}  # type: LoopWarps

    for sym in symbols.keys():
        match = pat.match(sym)
        if match is None:
            continue

        count_from = int(match.group(1))
        count_to = int(match.group(2))
        addr = symbols[sym]
        assert isinstance(addr, int)

        if count_to < count_from:
            raise RuntimeError('Loop warp instruction from symbol {!r}'
                               'implies an infinite loop (because {} < {}).'
                               .format(sym, count_to, count_from))

        at_addr = ret.setdefault(addr, {})
        if count_from in at_addr:
            raise RuntimeError('Multiple symbols specify a loop warp at {:#x} '
                               'with a starting count of {}.'
                               .format(addr, count_from))

        at_addr[count_from] = count_to

    return ret


def load_elf(sim: OTBNSim, path: str) -> Optional[int]:
    '''Load ELF file at path and inject its contents into sim

    Returns the expected end address, if set, otherwise None.

    '''
    (imem_bytes, dmem_bytes, symbols) = read_elf(path)

    # Collect imem bytes into 32-bit words and set the validity bit for each
    assert len(imem_bytes) & 3 == 0
    imem_words = [(True, w32s[0])
                  for w32s in struct.iter_unpack('<I', imem_bytes)]

    imem_insns = decode_words(0, imem_words)
    loop_warps = _get_loop_warps(symbols)
    exp_end = _get_exp_end_addr(symbols)

    sim.load_program(imem_insns)
    sim.loop_warps = loop_warps
    sim.load_data(dmem_bytes, has_validity=False)

    return exp_end
