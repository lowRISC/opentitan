# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


class Trace:
    '''An object that can cause a trace entry'''

    def trace(self) -> str:
        '''Return a representation of the entry for tracing

        This is used by things like the standalone ISS with -v

        '''
        raise NotImplementedError()


class TracePC(Trace):
    def __init__(self, pc: int):
        self.pc = pc

    def trace(self) -> str:
        return "pc = {:#x}".format(self.pc)
