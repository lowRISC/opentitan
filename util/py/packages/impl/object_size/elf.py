# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path

from elftools import elf
from elftools.elf import elffile

from util.py.packages.impl.object_size.memory import find_memory_of_addr
from util.py.packages.impl.object_size.types import Memory, Section, Symbol
from util.py.packages.lib.ot_logging import log


def get_segment_of_section(elf: elffile.ELFFile, section):
    for segment in elf.iter_segments():
        if segment.section_in_segment(section):
            return segment
    raise RuntimeError(
        f"Could not find the segment that {section.name} belongs to")
    return None


def parse_section(section: elf.sections.Section,
                  segment: elf.segments.Segment) -> Section:
    vma = section['sh_addr']
    if section['sh_type'] == "SHT_NOBITS":
        lma = "NOBITS"
    elif section['sh_size'] == 0:
        lma = "empty"
    else:
        lma = segment["p_paddr"] + section["sh_offset"] - segment["p_offset"]
    memories = [find_memory_of_addr(vma)]
    if isinstance(lma, int) and vma != lma:
        lma_memory = find_memory_of_addr(lma)
        assert (lma_memory != memories[0])
        memories.append(lma_memory)
    return Section(name=section.name,
                   memories=memories,
                   vma=vma,
                   lma=lma,
                   size=section['sh_size'],
                   alignment=section['sh_addralign'],
                   symbols=[],
                   type_=section['sh_type'],
                   flags=hex(section['sh_flags']))


def parse_symbol(sym, elf, sections):
    si = sym['st_shndx']
    if isinstance(si, str):
        log.info(f"Skipping symbol with string section index: {si}")
        return None
    section_name = elf.get_section(si).name
    section = sections.get(section_name, None)
    if not section:
        log.info(
            f"Skipping symbol {sym.name} from skipped section {section_name}")
        return None
    size = sym['st_size']
    if size == 0:
        log.info(f"Skipping empty symbol {sym.name}")
        return None
    if section.lma == "NOBITS":
        lma = "NOBITS"
    else:
        lma = sym['st_value'] - (section.vma - section.lma)
    symbol = Symbol(name=sym.name,
                    section=section.name,
                    vma=sym['st_value'],
                    lma=lma,
                    size=sym['st_size'],
                    type_=sym['st_info']['type'],
                    binding=sym['st_info']['bind'],
                    visibility=sym['st_other']['visibility'],
                    file_=0,
                    line=0)
    return symbol


def parse_elf_file(path: Path, memories: dict[str,
                                              Memory]) -> dict[str, Section]:
    sections = {}
    with path.open('rb') as f:
        elf = elffile.ELFFile(f)
        for section in elf.iter_sections():
            if section['sh_type'] not in [
                    "SHT_PROGBITS", "SHT_NOBITS"
            ] or (section['sh_flags'] & 0x7 == 0) or (section['sh_size'] == 0):
                log.info(f"Skipping section '{section.name}', "
                         f"type: '{section['sh_type']}', "
                         f"flags: {section['sh_flags']}, "
                         f"size:{section['sh_size']}")
                continue
            segment = get_segment_of_section(elf, section)
            parsed = parse_section(section, segment)
            sections[parsed.name] = parsed

        symbol_table = elf.get_section_by_name('.symtab')
        for symbol in symbol_table.iter_symbols():
            sym = parse_symbol(symbol, elf, sections)
            if sym:
                section = sections[sym.section]
                section.symbols.append(sym)
                for sec_mem in section.memories:
                    memories[sec_mem].symbols.append(sym)
    return sections
