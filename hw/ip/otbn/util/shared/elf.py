# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''OTBN ELF file handling'''

from typing import List, Optional, Tuple, Dict

from elftools.elf.elffile import ELFFile, SymbolTableSection  # type: ignore

from .mem_layout import get_memory_layout

_SegList = List[Tuple[int, bytes]]

# A _MemDesc is a pair (lma, length). length should be non-negative.
_MemDesc = Tuple[int, int]


def _flatten_segments(segments: _SegList, mem_desc: _MemDesc) -> bytes:
    '''Write the given ELF segments to a block of bytes

    Let (block_lma, block_len) = _MemDesc. The segments are assumed to be
    disjoint. The segment with the smallest address is assumed to start
    somewhere above block_lma and the segment with the highest address is
    assumed to finish less than block_len bytes above block_lma.

    The returned block of bytes will have length at most block_len. Any
    internal gaps are padded with zeroes.

    '''
    block_lma, block_len = mem_desc
    assert 0 <= block_len

    lma = block_lma
    chunks = []

    # Walk through the segments in increasing order of LMA.
    for seg_lma, seg_data in sorted(segments, key=lambda pr: pr[0]):
        assert lma <= seg_lma
        if lma < seg_lma:
            chunks.append(b'\x00' * (seg_lma - lma))
            lma = seg_lma

        chunks.append(seg_data)
        lma += len(seg_data)

    assert block_lma <= lma

    block_top = block_lma + block_len
    assert lma <= block_top

    return b''.join(chunks)


def _get_elf_mem_data(elf_file: ELFFile,
                      imem_desc: _MemDesc,
                      dmem_desc: _MemDesc) -> Tuple[bytes, bytes]:
    '''Extract imem/dmem segments from elf_file'''
    imem_segments = []
    dmem_segments = []

    imem_lma, imem_len = imem_desc
    dmem_lma, dmem_len = dmem_desc

    imem_top = imem_lma + imem_len
    dmem_top = dmem_lma + dmem_len

    assert imem_lma <= imem_top
    assert dmem_lma <= dmem_top

    for segment in elf_file.iter_segments():
        seg_type = segment['p_type']

        # We're only interested in PT_LOAD segments
        if seg_type != 'PT_LOAD':
            continue

        seg_lma = segment['p_paddr']
        seg_top = seg_lma + segment['p_memsz']

        # Does this match an expected imem or dmem address?
        if imem_lma <= seg_lma <= imem_top:
            if seg_top > imem_top:
                raise RuntimeError('Segment has LMA range {:#x}..{:#x}, '
                                   'which intersects the IMEM range '
                                   '({:#x}..{:#x}), but is not fully '
                                   'contained in it.'
                                   .format(seg_lma, seg_top,
                                           imem_lma, imem_top))
            imem_segments.append((seg_lma, segment.data()))
            continue

        if dmem_lma <= seg_lma <= dmem_top:
            if seg_top > dmem_top:
                raise RuntimeError('Segment has LMA range {:#x}..{:#x}, '
                                   'which intersects the DMEM range '
                                   '({:#x}..{:#x}), but is not fully '
                                   'contained in it.'
                                   .format(seg_lma, seg_top,
                                           dmem_lma, dmem_top))
            dmem_segments.append((seg_lma, segment.data()))
            continue

        # We shouldn't have any loadable segments that don't look like
        # either IMEM or DMEM.
        raise RuntimeError("Segment has LMA {:#x}, which doesn't start in "
                           "IMEM range (base {:#x}) or DMEM range "
                           "(base {:#x})."
                           .format(seg_lma, imem_lma, dmem_lma))

    imem_bytes = _flatten_segments(imem_segments, imem_desc)
    dmem_bytes = _flatten_segments(dmem_segments, dmem_desc)

    return (imem_bytes, dmem_bytes)


def _get_symtab(elf_file: ELFFile) -> Optional[SymbolTableSection]:
    '''Get the symbol table from elf_file if there is one'''
    section = elf_file.get_section_by_name('.symtab')
    if section is None:
        # No symbol table found
        return None

    if not isinstance(section, SymbolTableSection):
        # Huh? The .symtab section isn't a symbol table?? Oh well, nevermind.
        return None

    return section


def read_elf(path: str) -> Tuple[bytes,
                                 bytes,
                                 Dict[str, int]]:
    '''Load the ELF file at path.

    Returns a tuple (imem_bytes, dmem_bytes, exp_end_addr, loop_warps). The
    first two coordinates are as returned by _get_elf_mem_data. exp_end_addr is
    as returned by _get_exp_end_addr. loop_warps is as returned by
    _get_loop_warps.

    '''
    mems = get_memory_layout()
    imem_desc = (mems.imem_address, mems.imem_size_bytes)
    dmem_desc = (mems.dmem_address, mems.dmem_bus_size_bytes)

    with open(path, 'rb') as handle:
        elf_file = ELFFile(handle)
        imem_bytes, dmem_bytes = _get_elf_mem_data(elf_file,
                                                   imem_desc, dmem_desc)
        symtab = _get_symtab(elf_file)
        symbols = {}
        if symtab is not None:
            for sym in symtab.iter_symbols():
                assert isinstance(sym['st_value'], int)
                symbols[sym.name] = sym['st_value']

    assert len(imem_bytes) <= imem_desc[1]
    if len(imem_bytes) & 3:
        raise RuntimeError('ELF file at {!r} has imem data of length {}: '
                           'not a multiple of 4.'
                           .format(path, len(imem_bytes)))

    return (imem_bytes, dmem_bytes, symbols)
