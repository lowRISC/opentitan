# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Tuple

from shared.insn_yaml import InsnsFile

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

    @staticmethod
    def from_json(insns_file: InsnsFile,
                  idx: int,
                  json: object) -> 'Snippet':
        '''The inverse of to_json.

        idx is the 0-based number of the snippet in the file, just used for
        error messages.

        '''
        if not isinstance(json, list):
            raise ValueError('Object for snippet {} is not a list.'
                             .format(idx))

        parts = []
        for idx1, part in enumerate(json):
            # Each element should be a pair: (addr, insns). This will have come
            # out as a list (since tuples serialize as lists).
            if not (isinstance(part, list) and len(part) == 2):
                raise ValueError('Part {} for snippet {} is not a pair.'
                                 .format(idx1, idx))

            addr, insns_json = part

            # The address should be an aligned non-negative integer and insns
            # should itself be a list (of serialized Insn objects).
            if not isinstance(addr, int):
                raise ValueError('First coordinate of part {} for snippet {} '
                                 'is not an integer.'
                                 .format(idx1, idx))
            if addr < 0:
                raise ValueError('Address of part {} for snippet {} is {}, '
                                 'but should be non-negative.'
                                 .format(idx1, idx, addr))
            if addr & 3:
                raise ValueError('Address of part {} for snippet {} is {}, '
                                 'but should be 4-byte aligned.'
                                 .format(idx1, idx, addr))

            if not isinstance(insns_json, list):
                raise ValueError('Second coordinate of part {} for snippet {} '
                                 'is not a list.'
                                 .format(idx1, idx))

            insns = []
            for insn_idx, insn_json in enumerate(insns_json):
                where = ('In snippet {}, part {}, instruction {}'
                         .format(idx, idx1, insn_idx))
                insns.append(ProgInsn.from_json(insns_file, where, insn_json))

            parts.append((addr, insns))

        return Snippet(parts)
