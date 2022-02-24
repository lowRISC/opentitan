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
                fuel: int,
                insns_file: InsnsFile) -> Tuple[InitData, Snippet, int]:
    '''Generate a random program for OTBN

    fuel gives a rough upper bound for the number of instructions that will be
    executed by the generated program.

    Returns (init_data, snippet, end_addr). init_data is a dict mapping (4-byte
    aligned) address to u32s that should be loaded into data memory before
    starting the program. snippets is a tree of instruction snippets. end_addr
    is the expected end address.

    '''

    # Find the size of the memory that we can access. Both memories start
    # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
    # for memory x, not the VMA)
    mems = get_memory_layout()

    program = Program(mems.imem_address, mems.imem_size_bytes,
                      mems.dmem_address, mems.dmem_size_bytes)
    model = Model(mems.dmem_size_bytes, fuel)

    # Generate some initialised data to start with. Otherwise, it takes a while
    # before we start issuing loads (because we need stores to happen first).
    # Tell the model that we've done so.
    #
    # Note that we only use the bus-accessible part of DMEM for initialised
    # data.
    init_data = InitData.gen(mems.dmem_bus_size_bytes)
    for addr in init_data.keys():
        model.touch_mem('dmem', addr, 4)

    try:
        gens = SnippetGens(config, insns_file)
    except ValueError as err:
        raise RuntimeError('Failed to initialise snippet generators: {}'
                           .format(err)) from None

    snippet, end_addr = gens.gen_program(model, program)
    return init_data, snippet, end_addr
