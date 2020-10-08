# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from riscvmodel.types import Trace  # type: ignore

from .flags import FlagGroups
from .wsr import WSRFile


class CSRFile:
    '''A model of the CSR file'''
    def __init__(self) -> None:
        self.flags = FlagGroups()

    def read_unsigned(self, wsrs: WSRFile, idx: int) -> int:
        if idx == 0x7c0:
            # FLAGS register
            return self.flags.read_unsigned()

        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]
            i = idx - 0x7d0
            mod_val = wsrs.MOD.read_unsigned()
            mask32 = (1 << 32) - 1
            return (mod_val >> (32 * i)) & mask32

        if idx == 0xfc0:
            # RND register
            return wsrs.RND.read_u32()

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def write_unsigned(self, wsrs: WSRFile, idx: int, value: int) -> None:
        assert 0 <= value < (1 << 32)

        if idx == 0x7c0:
            # FLAGS register
            self.flags.write_unsigned(value)
            return

        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]. read,modify,write.
            i = idx - 0x7d0
            old_val = wsrs.MOD.read_unsigned()
            shifted_mask = ((1 << 32) - 1) << (32 * i)
            cleared = old_val & ~shifted_mask
            new_val = cleared | (value << (32 * i))
            wsrs.MOD.write_unsigned(new_val)
            return

        if idx == 0xfc0:
            # RND register (writes are ignored)
            return

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))
