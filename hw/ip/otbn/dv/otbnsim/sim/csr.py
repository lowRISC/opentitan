# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
from typing import Any, Callable, Dict, List, Optional
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


class MaiOperation(IntEnum):
    A2B = 0
    B2A = 1
    SECADD = 2


class MaiCtrlCSR(DumbISPR):
    '''Models the MAI CTRL CSR'''
    def __init__(self) -> None:
        super().__init__("MAI_CTRL", 32)
        self.START_BIT_MASK = 0x1
        self.START_BIT_OFFSET = 0
        self.OPERATION_MASK = 0x3
        self.OPERATION_OFFSET = 1

    def on_start(self) -> None:
        super().on_start()
        # On start, the default operation is set.
        self._value |= (MaiOperation.A2B & self.OPERATION_MASK) << self.OPERATION_OFFSET

    def read_start_bit(self) -> bool:
        '''Get the start bit from the CSR.'''
        bit = (self.read_unsigned() >> self.START_BIT_OFFSET) & self.START_BIT_MASK
        return bit != 0

    def would_set_start_bit(self, value: int) -> bool:
        '''Return whether writing value would set the start bit.'''
        return ((value >> self.START_BIT_OFFSET) & self.START_BIT_MASK) != 0

    def set_start_bit(self, start: bool) -> None:
        '''Set or clear the start bit in the CSR.

        This takes effect immediately. Note that we still report the change to generate a proper
        trace. Any "simultaneous" write by an instruction will override this change.
        '''
        val = self.read_unsigned()
        if start:
            val |= self.START_BIT_MASK << self.START_BIT_OFFSET
        else:
            val &= ~(self.START_BIT_MASK << self.START_BIT_OFFSET)
        self._value = val
        self._next_value = val
        self._pending_write = True

    def read_operation(self) -> MaiOperation:
        '''Get the operation field from the CSR.'''
        op = (self.read_unsigned() >> self.OPERATION_OFFSET) & self.OPERATION_MASK
        # The enum cast will fail if the current operation is not a valid option. If this happens
        # something before went wrong as we only allow writing valid options.
        return MaiOperation(op)

    def is_valid_operation(self, value: int) -> bool:
        '''Returns whether the CSR value contains valid operation bits.'''
        op = (value >> self.OPERATION_OFFSET) & self.OPERATION_MASK
        # TODO: Clean this up once we have python 3.12+
        return op in MaiOperation._value2member_map_

    def would_change_op(self, value: int) -> bool:
        '''Return whether writing value to the CSR would change the operation field.
        The value to be checked must specify a valid operation option.
        '''
        new_op = MaiOperation((value >> self.OPERATION_OFFSET) & self.OPERATION_MASK)
        curr_op = self.read_operation()
        return new_op != curr_op


class MaiStatusCSR(DumbISPR):
    '''Models the MAI STATUS CSR'''
    def __init__(self) -> None:
        super().__init__("MAI_STATUS", 32)
        self.BUSY_BIT_MASK = 0x1
        self.BUSY_BIT_OFFSET = 0
        self.READY_BIT_MASK = 0x1
        self.READY_BIT_OFFSET = 1

    def on_start(self) -> None:
        super().on_start()
        # On start, the MAI is not busy and is ready for new inputs.
        self._value |= self.READY_BIT_MASK << self.READY_BIT_OFFSET

    def write_unsigned(self, value: int) -> None:
        '''Ignore writes to the MAI STATUS CSR.
        Note this is different from set_ methods. This is used by instructions and the set_ methods
        are used directly by the MAI.'''
        return

    def read_ready_bit(self) -> bool:
        '''Get the ready bit from the CSR.'''
        bit = (self.read_unsigned() >> self.READY_BIT_OFFSET) & self.READY_BIT_MASK
        return bit != 0

    def set_ready_bit(self, ready: bool) -> None:
        '''Set or clear the ready bit in the CSR.
        This takes effect immediately. Note that we still report the change to generate a proper
        trace.'''
        val = self.read_unsigned()
        if ready:
            val |= self.READY_BIT_MASK << self.READY_BIT_OFFSET
        else:
            val &= ~(self.READY_BIT_MASK << self.READY_BIT_OFFSET)
        self._value = val
        self._next_value = val
        self._pending_write = True

    def write_ready_bit(self, ready: bool) -> None:
        '''Set or clear the ready bit in the CSR.
        This takes effect when committing.'''
        # Check if any other bit manipulation is pending. If so, we must use the pending value to
        # avoid discarding the previous write.
        val = self._next_value if self._pending_write else self.read_unsigned()
        # _pending_write should never be set if _next_value is None.
        assert val is not None
        if ready:
            val |= (self.READY_BIT_MASK << self.READY_BIT_OFFSET)
        else:
            val &= ~(self.READY_BIT_MASK << self.READY_BIT_OFFSET)
        # We cannot use self.write_unsigned here as any write from an instruction is ignored.
        self._next_value = val
        self._pending_write = True

    def read_busy_bit(self) -> bool:
        '''Get the busy bit from the CSR.'''
        bit = (self.read_unsigned() >> self.BUSY_BIT_OFFSET) & self.BUSY_BIT_MASK
        return bit != 0

    def set_busy_bit(self, busy: bool) -> None:
        '''Set or clear the busy bit in the CSR.
        This takes effect immediately. Note that we still report the change to generate a proper
        trace.'''
        val = self.read_unsigned()
        if busy:
            val |= (self.BUSY_BIT_MASK << self.BUSY_BIT_OFFSET)
        else:
            val &= ~(self.BUSY_BIT_MASK << self.BUSY_BIT_OFFSET)
        self._value = val
        self._next_value = val
        self._pending_write = True

    def write_busy_bit(self, busy: bool) -> None:
        '''Set or clear the busy bit in the CSR.
        This takes effect when committing.'''
        # Check if any other bit manipulation is pending. If so, we must use the pending value to
        # avoid discarding the previous write.
        val = self._next_value if self._pending_write else self.read_unsigned()
        # _pending_write should never be set if _next_value is None.
        assert val is not None
        if busy:
            val |= (self.BUSY_BIT_MASK << self.BUSY_BIT_OFFSET)
        else:
            val &= ~(self.BUSY_BIT_MASK << self.BUSY_BIT_OFFSET)
        # We cannot use self.write_unsigned here as any write from an instruction is ignored.
        self._next_value = val
        self._pending_write = True


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
            0x7f0,  # MAI_CTRL
            0xfc0,  # RND
            0xfc1,  # URND
            0xfc2,  # KMAC_STATUS
            0xfc3,  # KMAC_ERROR
            0xfe0,  # MAI_STATUS
        }

        self._idx_to_csr: Dict[int, Any] = {
            0x7c0: self.flags.groups[0],
            0x7c1: self.flags.groups[1],
            0x7c8: self.flags,
            0x7d8: self.RND_PREFETCH,
            0x7d9: self.KMAC_IF_STATUS,
            0x7da: self.KMAC_INTR,
            0x7db: self.KMAC_CFG,
            0x7dc: self.KMAC_MSG_SEND,
            0x7dd: self.KMAC_CMD,
            0x7de: self.KMAC_BYTE_STROBE,
            0x7f0: self.MAI_CTRL,
            0xfc0: self.RND,
            0xfc1: self.URND,
            0xfc2: self.KMAC_STATUS,
            0xfc3: self.KMAC_ERROR,
            0xfe0: self.MAI_STATUS,
        }

        self.on_start()

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

    def on_start(self) -> None:
        '''Reset CSRs and flags when starting an operation'''
        self.flags = FlagGroups()
        self.MaiCtrl.on_start()
        self.MaiStatus.on_start()

    def check_idx(self, idx: int) -> bool:
        '''Return True if idx points to a valid CSR; False otherwise.'''
        return idx in self._known_indices

    def read_unsigned(self, wsrs: WSRFile, idx: int) -> int:
        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]
            mod_n = idx - 0x7d0
            return self._get_field(mod_n, 32, wsrs.MOD.read_unsigned())

        csr = self._idx_to_csr.get(idx)
        if csr is not None:
            return int(csr.read_unsigned())

        if idx == 0xfe0:
            # MAI_STATUS register
            return self.MaiStatus.read_unsigned()

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def write_unsigned(self, wsrs: WSRFile, idx: int, value: int) -> None:
        assert 0 <= value < (1 << 32)

        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]. read,modify,write.
            mod_n = idx - 0x7d0
            old = wsrs.MOD.read_unsigned()
            wsrs.MOD.write_unsigned(self._set_field(mod_n, 32, value, old))
            return

        csr = self._idx_to_csr.get(idx)
        if csr is not None:
            csr.write_unsigned(value)
            return

        if idx == 0xfe0:
            # MAI_STATUS register (which ignores writes)
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
