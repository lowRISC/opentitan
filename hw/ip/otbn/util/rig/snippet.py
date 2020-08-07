# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Tuple

from .program import ProgInsn, Program


class Snippet:
    '''A collection of instructions, generated as part of a random program.

    parts is a list of pairs (addr, insns), where insns is a nonempty list of
    instructions and addr is the address of its first element. The entry point
    for the snippet is the address of the first part.

    '''
    def __init__(self,
                 parts: List[Tuple[int, List[ProgInsn]]]):
        assert parts
        for idx, (addr, insns) in enumerate(parts):
            assert addr >= 0
            assert addr & 3 == 0

        self.parts = parts

    def insert_into_program(self, program: Program) -> None:
        '''Insert this snippet into the given program

        This assumes the parts of the snippet are disjoint from the existing
        instructions in the program.

        '''
        for addr, insns in self.parts:
            program.add_insns(addr, insns)

    def to_json(self) -> object:
        '''Serialize to an object that can be written as JSON'''
        lst = []
        for addr, insns in self.parts:
            lst.append((addr, [i.to_json() for i in insns]))
        return lst
