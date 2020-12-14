# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Tuple

from shared.insn_yaml import InsnsFile
from shared.mem_layout import get_memory_layout

from .init_data import InitData
from .program import Program
from .model import Model
from .snippet_gens import SnippetGens
from .snippet import Snippet


def gen_program(start_addr: int,
                size: int,
                insns_file: InsnsFile) -> Tuple[InitData, List[Snippet]]:
    '''Generate a random program for OTBN

    start_addr is the reset address (the value that should be programmed into
    the START_ADDR register). size gives a rough upper bound for the number of
    instructions that will be executed by the generated program.

    Returns (init_data, snippets, program). init_data is a dict mapping (4-byte
    aligned) address to u32s that should be loaded into data memory before
    starting the program. snippets is a list of instruction snippets. program
    is the generated program (from flattening them both).

    '''

    # Find the size of the memory that we can access. Both memories start
    # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
    # for memory x, not the VMA)
    mems = get_memory_layout()
    imem_lma, imem_size = mems['IMEM']
    dmem_lma, dmem_size = mems['DMEM']

    assert start_addr <= imem_size - 4
    assert start_addr & 3 == 0

    program = Program(imem_lma, imem_size, dmem_lma, dmem_size)
    model = Model(dmem_size, start_addr)

    # Generate some initialised data to start with. Otherwise, it takes a while
    # before we start issuing loads (because we need stores to happen first).
    # Tell the model that we've done so.
    init_data = InitData.gen(dmem_size)
    for addr in init_data.keys():
        model.touch_mem('dmem', addr, 4)

    generators = SnippetGens(insns_file)
    snippets = []

    while size > 0:
        snippet, done, new_size = generators.gen(size, model, program)
        snippets.append(snippet)
        if done:
            break

        # Each new snippet should consume some of size to guarantee
        # termination.
        assert new_size < size
        size = new_size

    return init_data, snippets


def snippets_to_program(snippets: List[Snippet]) -> Program:
    '''Write a series of disjoint snippets to make a program'''
    # Find the size of the memory that we can access. Both memories start
    # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
    # for memory x, not the VMA)
    mems = get_memory_layout()
    imem_lma, imem_size = mems['IMEM']
    dmem_lma, dmem_size = mems['DMEM']
    program = Program(imem_lma, imem_size, dmem_lma, dmem_size)

    for snippet in snippets:
        snippet.insert_into_program(program)

    return program
