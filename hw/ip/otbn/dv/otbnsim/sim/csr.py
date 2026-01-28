# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List
from .flags import FlagGroups
from .ispr import DumbISPR
from .kmac_ispr import (
    KmacCfgCSR,
    KmacCmdCSR,
    KmacMsgSemdCSR,
    KmacStatusCSR,
    KmacErrorCSR,
    KmacIfStatusCSR,
    KmacIntrCSR,
)
from .trace import Trace
from .wsr import WSRFile


class CSRFile:
    '''A model of the CSR file'''
    def __init__(self) -> None:
        self.flags = FlagGroups()
        self.KMAC_STATUS = KmacStatusCSR('KMAC_STATUS')
        self.KMAC_IF_STATUS = KmacIfStatusCSR('KMAC_IF_STATUS')
        self.KMAC_INTR = KmacIntrCSR('KMAC_INTR')
        self.KMAC_ERROR = KmacErrorCSR('KMAC_ERROR')
        self.KMAC_CFG = KmacCfgCSR('KMAC_CFG')
        self.KMAC_MSG_SEND = KmacMsgSemdCSR('KMAC_MSG_SEND')
        self.KMAC_CMD = KmacCmdCSR('KMAC_CMD')
        self.KMAC_BYTE_STROBE = DumbISPR('KMAC_BYTE_STROBE', 32)

        self._known_indices = {
            0x7c0,  # FG0
            0x7c1,  # FG1
            0x7c8,  # FLAGS
            *range(0x7d0, 0x7d8),  # MODi
            0x7d8,  # RND_PREFETCH
            0x7d9,  # KMAC_IF_STATUS
            0x7da,  # KMAC_INTR
            0x7db,  # KMAC_CFG
            0x7dc,  # KMAC_MSG_SEND
            0x7dd,  # KMAC_CMD
            0x7de,  # KMAC_BYTE_STROBE
            0xfc0,  # RND
            0xfc1,  # URND
            0xfc2,  # KMAC_STATUS
            0xfc3,  # KMAC_ERROR
        }

        self._by_idx = {
            0x7d9: self.KMAC_IF_STATUS,
            0x7da: self.KMAC_INTR,
            0x7db: self.KMAC_CFG,
            0x7dc: self.KMAC_MSG_SEND,
            0x7dd: self.KMAC_CMD,
            0x7de: self.KMAC_BYTE_STROBE,
            0xfc2: self.KMAC_STATUS,
            0xfc3: self.KMAC_ERROR,
        }

    @staticmethod
    def _get_field(field_idx: int, field_size: int, val: int) -> int:
        mask = (1 << field_size) - 1
        return (val >> (field_size * field_idx)) & mask

    @staticmethod
    def _set_field(field_idx: int, field_size: int, field_val: int,
                   old_val: int) -> int:
        assert 0 <= field_val < (1 << field_size)
        mask = (1 << field_size) - 1
        shift = field_size * field_idx
        return (old_val & ~(mask << shift)) | (field_val << shift)

    def check_idx(self, idx: int) -> bool:
        '''Return True if idx points to a valid CSR; False otherwise.'''
        return idx in self._known_indices

    def read_unsigned(self, wsrs: WSRFile, idx: int) -> int:
        if 0x7c0 <= idx <= 0x7c1:
            # FG0/FG1
            fg = idx - 0x7c0
            return self._get_field(fg, 4, self.flags.read_unsigned())

        if idx == 0x7c8:
            # FLAGS register
            return self.flags.read_unsigned()

        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]
            mod_n = idx - 0x7d0
            return self._get_field(mod_n, 32, wsrs.MOD.read_unsigned())

        if idx == 0x7d8:
            # RND_PREFETCH register
            return 0

        if idx in {0x7d9, 0x7da, 0x7db, 0x7dc, 0x7dd, 0x7de, 0xfc2, 0xfc3}:
            # Read KMAC register
            return self._by_idx[idx].read_unsigned()

        if idx == 0xfc0:
            # RND register
            return wsrs.RND.read_u32()

        if idx == 0xfc1:
            # URND register
            return wsrs.URND.read_u32()

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def write_unsigned(self, wsrs: WSRFile, idx: int, value: int) -> None:
        assert 0 <= value < (1 << 32)

        if 0x7c0 <= idx <= 0x7c1:
            # FG0/FG1
            fg = idx - 0x7c0
            old = self.flags.read_unsigned()
            self.flags.write_unsigned(self._set_field(fg, 4, value & 0xf, old))
            return

        if idx == 0x7c8:
            # FLAGS register
            self.flags.write_unsigned(value)
            return

        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]. read,modify,write.
            mod_n = idx - 0x7d0
            old = wsrs.MOD.read_unsigned()
            wsrs.MOD.write_unsigned(self._set_field(mod_n, 32, value, old))
            return

        if idx == 0x7d8:
            # RND_PREFETCH
            wsrs.RND.request_value()
            return

        if idx in {0x7d9, 0x7da, 0x7db, 0x7dc, 0x7dd, 0x7de}:
            # Write to KMAC register.
            return self._by_idx[idx].write_unsigned(value)

        if idx in {0xfc0, 0xfc1, 0xfc2, 0xfc3}:
            # Ignore writes to these registers.
            return

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def commit(self) -> None:
        self.flags.commit()
        self.KMAC_STATUS.commit()
        self.KMAC_IF_STATUS.commit()
        self.KMAC_INTR.commit()
        self.KMAC_ERROR.commit()
        self.KMAC_CFG.commit()
        self.KMAC_MSG_SEND.commit()
        self.KMAC_CMD.commit()
        self.KMAC_BYTE_STROBE.commit()

    def abort(self) -> None:
        self.flags.abort()
        self.KMAC_STATUS.abort()
        self.KMAC_IF_STATUS.abort()
        self.KMAC_INTR.abort()
        self.KMAC_ERROR.abort()
        self.KMAC_CFG.abort()
        self.KMAC_MSG_SEND.abort()
        self.KMAC_CMD.abort()
        self.KMAC_BYTE_STROBE.abort()

    def changes(self) -> List[Trace]:
        ret: List[Trace] = []
        ret += self.flags.changes()
        ret += self.KMAC_STATUS.changes()
        ret += self.KMAC_IF_STATUS.changes()
        ret += self.KMAC_INTR.changes()
        ret += self.KMAC_ERROR.changes()
        ret += self.KMAC_CFG.changes()
        ret += self.KMAC_MSG_SEND.changes()
        ret += self.KMAC_CMD.changes()
        ret += self.KMAC_BYTE_STROBE.changes()
        return ret

    def wipe(self) -> None:
        self.flags.write_unsigned(0)
