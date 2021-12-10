#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from shared.decode import OTBNProgram


class CodeSection:
    '''A continuous part of a program's code (represented as a PC range).

    The code section is considered to include both the start and end PC.
    '''
    def __init__(self, start: int, end: int):
        self.start = start
        self.end = end

    def get_insn_sequence(self, program: OTBNProgram):
        return [
            program.get_insn(pc) for pc in range(self.start, self.end + 4, 4)
        ]

    def __contains__(self, pc: int):
        return self.start <= pc and pc <= self.end

    def __repr__(self):
        return '0x{:x}-0x{:x}'.format(self.start, self.end)
