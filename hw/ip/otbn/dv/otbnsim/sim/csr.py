# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
from typing import List, Optional, Sequence

from .flags import FlagGroups
from .trace import Trace
from .wsr import WSRFile


class TraceCSR(Trace):
    def __init__(self, csr_name: str, new_value: Optional[int]):
        self.csr_name = csr_name
        self.new_value = new_value

    def trace(self) -> str:
        s = '{} = '.format(self.csr_name)
        if self.new_value is None:
            s += '0x' + 'x' * 8
        else:
            s += '{:#x}'.format(self.new_value)
        return s

    def rtl_trace(self) -> str:
        return '> {}: {}'.format(self.csr_name,
                                 Trace.hex_value(self.new_value, 32))


class CSR:
    '''Models a Control and Status Register'''
    def __init__(self, name: str):
        self.name = name
        self._pending_write = False

    def has_value(self) -> bool:
        '''Return whether the CSR has a valid value'''
        return True

    def on_start(self) -> None:
        '''Reset the CSR if necessary for the start of an operation'''
        return

    def read_unsigned(self) -> int:
        '''Get the stored value as a 32-bit unsigned value'''
        raise NotImplementedError()

    def write_unsigned(self, value: int) -> None:
        '''Set the stored value as a 32-bit unsigned value'''
        raise NotImplementedError()

    def read_signed(self) -> int:
        '''Get the stored value as a 32-bit signed value'''
        uval = self.read_unsigned()
        return uval - (1 << 32 if uval >> 31 else 0)

    def write_signed(self, value: int) -> None:
        '''Set the stored value as a 32-bit signed value'''
        assert -(1 << 32) <= value < (1 << 31)
        uval = (1 << 32) + value if value < 0 else value
        self.write_unsigned(uval)

    def commit(self) -> None:
        '''Commit pending changes'''
        self._pending_write = False

    def abort(self) -> None:
        '''Abort pending changes'''
        self._pending_write = False

    def changes(self) -> Sequence[Trace]:
        '''Return list of pending architectural changes'''
        return []


class DumbCSR(CSR):
    '''Models a CSR without special behaviour'''
    def __init__(self, name: str):
        super().__init__(name)
        self._value = 0
        self._next_value: Optional[int] = None

    def on_start(self) -> None:
        self._value = 0
        self._next_value = None

    def read_unsigned(self) -> int:
        return self._value

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << 32)
        self._next_value = value
        self._pending_write = True

    def write_invalid(self) -> None:
        self._next_value = None
        self._pending_write = True

    def commit(self) -> None:
        if self._next_value is not None:
            self._value = self._next_value
        self._next_value = None
        self._pending_write = False

    def abort(self) -> None:
        self._next_value = None
        self._pending_write = False

    def changes(self) -> List[TraceCSR]:
        return ([TraceCSR(self.name, self._next_value)]
                if self._pending_write else [])


class MaiOperation(IntEnum):
    A2B = 0
    B2A = 1
    SECADD = 2


class MaiCtrlCSR(DumbCSR):
    '''Models the MAI CTRL CSR'''
    def __init__(self) -> None:
        super().__init__("MAI_CTRL")
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


class MaiStatusCSR(DumbCSR):
    '''Models the MAI STATUS CSR'''
    def __init__(self) -> None:
        super().__init__("MAI_STATUS")
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
        Note this is different to set_ methods. This is used by instructions and the set_ methods
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
    def __init__(self) -> None:
        self.flags = FlagGroups()
        self.MaiCtrl = MaiCtrlCSR()
        self.MaiStatus = MaiStatusCSR()

        self._known_indices = set()
        self._known_indices.add(0x7c0)  # FG0
        self._known_indices.add(0x7c1)  # FG1
        self._known_indices.add(0x7c8)  # FLAGS
        for idx in range(0x7d0, 0x7d8):
            self._known_indices.add(idx)  # MODi
        self._known_indices.add(0x7d8)  # RND_PREFETCH
        self._known_indices.add(0x7f0)  # MAI_CTRL
        self._known_indices.add(0xfc0)  # RND
        self._known_indices.add(0xfc1)  # URND
        self._known_indices.add(0xfe0)  # MAI_STATUS

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

        if idx == 0x7f0:
            # MAI_CTRL register
            return self.MaiCtrl.read_unsigned()

        if idx == 0xfc0:
            # RND register
            return wsrs.RND.read_u32()

        if idx == 0xfc1:
            # URND register
            return wsrs.URND.read_u32()

        if idx == 0xfe0:
            # MAI_STATUS register
            return self.MaiStatus.read_unsigned()

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

        if idx == 0x7f0:
            # MAI_CTRL register
            self.MaiCtrl.write_unsigned(value)
            return

        if idx == 0xfc0:
            # RND register (which ignores writes)
            return

        if idx == 0xfc1:
            # URND register (which ignores writes)
            return

        if idx == 0xfe0:
            # MAI_STATUS register (which ignores writes)
            return

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def wipe(self) -> None:
        self.flags.write_unsigned(0)
        # TODO: Wipe or reset MAI CTRL/STATUS?

    def commit(self) -> None:
        self.flags.commit()
        self.MaiCtrl.commit()
        self.MaiStatus.commit()

    def abort(self) -> None:
        self.flags.abort()
        self.MaiCtrl.abort()
        # The MAI_STATUS is always committed because only the MAI updates it.
        self.MaiStatus.commit()

    def changes(self) -> List[Trace]:
        traces: List[Trace] = []
        traces += self.flags.changes()
        traces += self.MaiCtrl.changes()
        traces += self.MaiStatus.changes()
        return traces
