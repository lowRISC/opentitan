#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Iterator, List

from shared.decode import OTBNProgram
from shared.insn_yaml import Insn


class CodeSection:
    '''A continuous part of a program's code (represented as a PC range).

    The code section is considered to include both the start and end PC.
    '''
    def __init__(self, start: int, end: int):
        self.start = start
        self.end = end

    def get_insn_sequence(self, program: OTBNProgram) -> List[Insn]:
        return [ program.get_insn(pc) for pc in self.__iter__() ]

    def pretty(self) -> str:
        return '0x{:x}-0x{:x}'.format(self.start, self.end)

    def __iter__(self) -> Iterator[int]:
        '''Iterates through PCs in the section.'''
        return iter(range(self.start, self.end + 4, 4))

    def __contains__(self, pc: int) -> bool:
        return self.start <= pc and pc <= self.end
