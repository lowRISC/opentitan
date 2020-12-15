# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional


class Trace:
    '''An object that can cause a trace entry'''

    def trace(self) -> str:
        '''Return a representation of the entry for tracing

        This is used by things like the standalone ISS with -v

        '''
        raise NotImplementedError()

    def rtl_trace(self) -> Optional[str]:
        '''Return a representation of the entry for RTL tracing

        This is used by the stepped interface (which gets compared with the RTL
        model). Return None if the RTL trace doesn't have an entry for this
        item (the default behaviour).

        '''
        return None

    @staticmethod
    def hex_value(value: int, bit_width: int) -> str:
        '''Render a hex value in the format expected by RTL tracing'''
        if bit_width == 32:
            return '{:#010x}'.format(value)

        num_words = (bit_width + 31) // 32
        mask32 = (1 << 32) - 1
        # Collect up words, LSB first
        words = []
        for idx in range(num_words):
            lsb = 32 * idx
            word = (value >> lsb) & mask32
            top_width = (bit_width - lsb + 3) // 4
            fmt_str = '{{:0{}x}}'.format(min(8, top_width))
            words.append(fmt_str.format(word))
        return '0x' + '_'.join(reversed(words))


class TracePC(Trace):
    def __init__(self, pc: int):
        self.pc = pc

    def trace(self) -> str:
        return "pc = {:#x}".format(self.pc)
