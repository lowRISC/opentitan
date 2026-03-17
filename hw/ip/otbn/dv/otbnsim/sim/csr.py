# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Any, Callable, Dict, List, Optional
from .constants import CsrAddrs
from .flags import FlagGroups
from .ispr import DumbISPR
from .kmac_ispr import (
    KmacCfgCSR,
    KmacCommandCSR,
    KmacStatusCSR,
    KmacErrorCSR,
    KmacIfStatusCSR,
    KmacIntrCSR,
)
from .mai_ispr import MaiCtrlCSR, MaiStatusCSR
from .trace import Trace
from .wsr import WSRFile


class WrapperCSR:
    """A CSR that delegates read/write logic to external callback functions.

    Useful for registers that map to non-standard logic.
    """

    def __init__(self,
                 read_func: Optional[Callable[[], int]] = None,
                 write_func: Optional[Callable[[int], Any]] = None):

        self._read_func = read_func if read_func else self._default_read
        self._write_func = write_func if write_func else self._default_write

    def _default_read(self) -> int:
        """Default behavior: Return 0"""
        return 0

    def _default_write(self, value: int) -> None:
        """Default behavior: Ineffective write"""
        return

    def read_unsigned(self) -> int:
        return self._read_func()

    def write_unsigned(self, value: int) -> None:
        self._write_func(value)


class CSRFile:
    '''A model of the CSR file'''
    def __init__(self, wsrs: WSRFile) -> None:
        self.flags = FlagGroups()
        self.RND_PREFETCH = WrapperCSR(
            write_func=lambda val: wsrs.RND.request_value()
        )
        self.KMAC_STATUS = KmacStatusCSR('KMAC_STATUS')
        self.KMAC_IF_STATUS = KmacIfStatusCSR('KMAC_IF_STATUS')
        self.KMAC_INTR = KmacIntrCSR('KMAC_INTR')
        self.KMAC_ERROR = KmacErrorCSR('KMAC_ERROR')
        self.KMAC_CFG = KmacCfgCSR('KMAC_CFG')
        self.KMAC_MSG_SEND = KmacCommandCSR('KMAC_MSG_SEND', write_mask=0x1)
        self.RND = WrapperCSR(read_func=wsrs.RND.read_u32)
        self.URND = WrapperCSR(read_func=wsrs.URND.read_u32)
        self.KMAC_CMD = KmacCommandCSR('KMAC_CMD', write_mask=0x3f)
        self.KMAC_BYTE_STROBE = DumbISPR('KMAC_BYTE_STROBE', width=32)
        self.MAI_CTRL = MaiCtrlCSR()
        self.MAI_STATUS = MaiStatusCSR()

        # This does not include all CSR addresses because:
        # - FG0 and FG1 map to the same underlying register.
        # - MOD0 .. MOD7 map to the MOD WSR.
        self._by_addr: Dict[CsrAddrs, Any] = {
            CsrAddrs.FLAGS: self.flags,
            CsrAddrs.RND_PREFETCH: self.RND_PREFETCH,
            CsrAddrs.KMAC_IF_STATUS: self.KMAC_IF_STATUS,
            CsrAddrs.KMAC_INTR: self.KMAC_INTR,
            CsrAddrs.KMAC_CFG: self.KMAC_CFG,
            CsrAddrs.KMAC_MSG_SEND: self.KMAC_MSG_SEND,
            CsrAddrs.KMAC_CMD: self.KMAC_CMD,
            CsrAddrs.KMAC_BYTE_STROBE: self.KMAC_BYTE_STROBE,
            CsrAddrs.MAI_CTRL: self.MAI_CTRL,
            CsrAddrs.RND: self.RND,
            CsrAddrs.URND: self.URND,
            CsrAddrs.KMAC_STATUS: self.KMAC_STATUS,
            CsrAddrs.KMAC_ERROR: self.KMAC_ERROR,
            CsrAddrs.MAI_STATUS: self.MAI_STATUS,
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
        # TODO: Clean this up once we have python 3.12+
        return idx in CsrAddrs._value2member_map_

    def read_unsigned(self, wsrs: WSRFile, idx: int) -> int:
        csr_addr = CsrAddrs(idx)

        # The flag groups are implemented as one physical register. Reading one flag group is
        # therefore actually a read from both groups.
        if CsrAddrs.FG0 <= csr_addr <= CsrAddrs.FG1:
            fg = csr_addr - CsrAddrs.FG0
            return self._get_field(fg, 4, self.flags.read_unsigned())

        if CsrAddrs.MOD0 <= csr_addr <= CsrAddrs.MOD7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]
            mod_n = csr_addr - CsrAddrs.MOD0
            return self._get_field(mod_n, 32, wsrs.MOD.read_unsigned())

        csr = self._by_addr.get(csr_addr)
        if csr is not None:
            return int(csr.read_unsigned())

        raise RuntimeError('Unhandled CSR index: {:#x}'.format(idx))

    def write_unsigned(self, wsrs: WSRFile, idx: int, value: int) -> None:
        assert 0 <= value < (1 << 32)
        csr_addr = CsrAddrs(idx)

        # The flag groups are impleme`  nted as one physical register. Writing to one flag group is
        # therefore actually a write to both groups.
        if CsrAddrs.FG0 <= csr_addr <= CsrAddrs.FG1:
            fg = csr_addr - CsrAddrs.FG0
            old = self.flags.read_unsigned()
            self.flags.write_unsigned(self._set_field(fg, 4, value & 0xf, old))
            return

        if CsrAddrs.MOD0 <= csr_addr <= CsrAddrs.MOD7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]. read,modify,write.
            mod_n = csr_addr - CsrAddrs.MOD0
            old = wsrs.MOD.read_unsigned()
            wsrs.MOD.write_unsigned(self._set_field(mod_n, 32, value, old))
            return

        csr = self._by_addr.get(csr_addr)
        if csr is not None:
            csr.write_unsigned(value)
            return

        raise RuntimeError('Unhandled CSR index: {:#x}'.format(idx))

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
        self.MAI_CTRL.commit()
        self.MAI_STATUS.commit()

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
        self.MAI_CTRL.abort()
        # The MAI_STATUS is always committed because only the MAI updates it.
        self.MAI_STATUS.commit()

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
        ret += self.MAI_CTRL.changes()
        ret += self.MAI_STATUS.changes()
        return ret

    def wipe(self) -> None:
        self.flags.write_unsigned(0)
        # TODO: Wipe or reset MAI CTRL/STATUS?
