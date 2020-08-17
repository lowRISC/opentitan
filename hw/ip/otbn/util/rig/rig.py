# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Tuple

from shared.insn_yaml import InsnsFile
from shared.mem_layout import get_memory_layout

from .program import Program
from .model import Model
from .snippet_gens import SnippetGens
from .snippet import Snippet


def gen_program(start_addr: int,
                size: int,
                insns_file: InsnsFile) -> Tuple[List[Snippet], Program]:
    '''Generate a random program for OTBN

    start_addr is the reset address (the value that should be programmed into
    the START_ADDR register). size gives a rough upper bound for the number of
    instructions that will be executed by the generated program.

    Returns (snippets, program) where snippets is a list of instruction
    snippets and program is the generated program.

    '''

    # Find the size of the memory that we can access. Both memories start
    # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
    # for memory x, not the VMA)
    mems = get_memory_layout()
    imem_lma, imem_size = mems['IMEM']
    dmem_size = mems['DMEM'][1]

    assert start_addr <= imem_size - 4
    assert start_addr & 3 == 0

    program = Program(imem_lma, imem_size)
    model = Model(dmem_size, start_addr)

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

    return snippets, program


def snippets_to_program(snippets: List[Snippet]) -> Program:
    '''Write a series of disjoint snippets to make a program'''
    # Find the size of the memory that we can access. Both memories start
    # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
    # for memory x, not the VMA)
    mems = get_memory_layout()
    imem_lma, imem_size = mems['IMEM']
    program = Program(imem_lma, imem_size)

    for snippet in snippets:
        snippet.insert_into_program(program)

    return program
