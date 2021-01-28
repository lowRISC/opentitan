# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Tuple

from shared.insn_yaml import InsnsFile
from shared.mem_layout import get_memory_layout

from .config import Config
from .init_data import InitData
from .program import Program
from .model import Model
from .snippet_gens import SnippetGens
from .snippet import Snippet


def gen_program(config: Config,
                start_addr: int,
                fuel: int,
                insns_file: InsnsFile) -> Tuple[InitData, Snippet]:
    '''Generate a random program for OTBN

    start_addr is the reset address (the value that should be programmed into
    the START_ADDR register). fuel gives a rough upper bound for the number of
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
    model = Model(dmem_size, start_addr, fuel)

    # Generate some initialised data to start with. Otherwise, it takes a while
    # before we start issuing loads (because we need stores to happen first).
    # Tell the model that we've done so.
    init_data = InitData.gen(dmem_size)
    for addr in init_data.keys():
        model.touch_mem('dmem', addr, 4)

    try:
        gens = SnippetGens(config, insns_file)
    except ValueError as err:
        raise RuntimeError('Failed to initialise snippet generators: {}'
                           .format(err)) from None

    snippet = gens.gen_rest(model, program)
    return init_data, snippet
