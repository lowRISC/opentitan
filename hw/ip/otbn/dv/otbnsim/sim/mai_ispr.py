# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
from typing import List, Optional
from .ispr import DumbISPR, ISPRChange


class MaiOperation(IntEnum):
    A2B = 0
    B2A = 1
    SECADD = 2


class MaiCtrlCSR(DumbISPR):
    '''Models the MAI CTRL CSR'''
    def __init__(self) -> None:
        self.START_BIT_MASK = 0x1
        self.START_BIT_OFFSET = 0
        self.OPERATION_MASK = 0x3
        self.OPERATION_OFFSET = 1
        super().__init__("MAI_CTRL", 32)
        self.on_start()

    def on_start(self) -> None:
        super().on_start()
        # On start, the default operation is set.
        self._operation = MaiOperation.A2B
        self._start_bit = False
        self._value = self._get_value()

    def _construct_value(self, start_bit: bool, operation: MaiOperation) -> int:
        '''Construct a register value based on a operation and start bit combination.'''
        raw = (((operation & self.OPERATION_MASK) << self.OPERATION_OFFSET) |
               (start_bit << self.START_BIT_OFFSET))
        assert 0 <= raw < (1 << self.width)
        return raw

    def _get_value(self) -> int:
        '''Construct the register value based on the current operation and start bit.'''
        return self._construct_value(self._start_bit, self._operation)

    def _extract_start_bit(self, value: int) -> bool:
        '''Extract the start bit from a register value.'''
        return ((value >> self.START_BIT_OFFSET) & self.START_BIT_MASK) != 0

    def _extract_operation(self, value: int) -> MaiOperation:
        '''Extract the operation field from a register value.
        The value to be checked must specify a valid operation option otherwise we crash.'''
        # If the conversion failed, the check when updating the operation did fail already.
        return MaiOperation((value >> self.OPERATION_OFFSET) & self.OPERATION_MASK)

    def _extract_fields(self, value: int) -> tuple[bool, MaiOperation]:
        '''Extract the fields from a register value.'''
        return self._extract_start_bit(value), self._extract_operation(value)

    def _update_fields(self, start_bit: Optional[bool] = None,
                       operation: Optional[MaiOperation] = None) -> None:
        '''Update all fields of the CSR based on the provided values.

        This takes effect immediately. Note that we still report the change to generate a proper
        trace.'''
        if start_bit is not None:
            self._start_bit = start_bit
        if operation is not None:
            self._operation = operation
        self._value = self._get_value()
        self._next_value = self._get_value()
        self._pending_write = True

    def commit(self) -> None:
        if self._next_value is not None:
            self._start_bit, self._operation = self._extract_fields(self._next_value)
            self._value = self._next_value
        self._next_value = None
        self._pending_write = False

    def is_start_bit_set(self) -> bool:
        '''Get the start bit from the CSR.'''
        return self._start_bit

    def would_set_start_bit(self, value: int) -> bool:
        '''Return whether writing value would set the start bit.'''
        return self._extract_start_bit(value)

    def update_start_bit(self, start: bool) -> None:
        '''Set or clear the start bit in the CSR.

        This takes effect immediately. Note that we still report the change to generate a proper
        trace. Any "simultaneous" write by an instruction will override this change.
        '''
        self._update_fields(start_bit=start)

    def current_operation(self) -> MaiOperation:
        '''Get the current operation.'''
        return self._operation

    def is_valid_operation(self, value: int) -> bool:
        '''Returns whether the value contains valid operation bits.'''
        try:
            # The extraction will fail if the value doesn't contain a valid operation.
            self._extract_operation(value)
            return True
        except ValueError:
            return False

    def would_change_op(self, value: int) -> bool:
        '''Return whether writing value to the CSR would change the operation field.
        The value to be checked must specify a valid operation option otherwise we crash.
        '''
        return self._extract_operation(value) != self.current_operation()

    # TODO: Remove this function once RTL also generates traces. Without the RTL traces the
    # simulation detects a trace mismatch and aborts.
    def changes(self) -> List[ISPRChange]:
        return []


class MaiStatusCSR(DumbISPR):
    '''Models the MAI STATUS CSR'''
    def __init__(self) -> None:
        self.BUSY_BIT_OFFSET = 0
        self.READY_BIT_OFFSET = 1
        super().__init__("MAI_STATUS", 32)
        self.on_start()

    def on_start(self) -> None:
        super().on_start()
        # On start, the MAI is not busy and is ready for new inputs.
        self._is_busy = False
        self._is_ready = True
        self._value = self._get_value()

    def write_unsigned(self, value: int) -> None:
        '''Ignore writes to the MAI STATUS CSR.

        Note this is different from update_ methods. This is used by instructions and the update_
        methods are used directly by the MAI hardware.'''
        return

    def _get_value(self) -> int:
        '''Construct the register value based on the current busy and ready bits.'''
        return ((self._is_busy << self.BUSY_BIT_OFFSET) | (self._is_ready << self.READY_BIT_OFFSET))

    def _update_bits(self, busy: Optional[bool] = None, ready: Optional[bool] = None) -> None:
        '''Set or clear the busy and ready bits in the CSR based on the provided values.

        This takes effect immediately. Note that we still report the change to generate a proper
        trace.'''
        if busy is not None:
            self._is_busy = busy
        if ready is not None:
            self._is_ready = ready
        self._value = self._get_value()
        self._next_value = self._get_value()
        self._pending_write = True

    def is_ready(self) -> bool:
        return self._is_ready

    def update_ready_bit(self, ready: bool) -> None:
        self._update_bits(ready=ready)

    def is_busy(self) -> bool:
        return self._is_busy

    def update_busy_bit(self, busy: bool) -> None:
        self._update_bits(busy=busy)

    # TODO: Remove this function once RTL also generates traces. Without the RTL traces the
    # simulation detects a trace mismatch and aborts.
    def changes(self) -> List[ISPRChange]:
        return []


class MaiOutputWSR(DumbISPR):
    def __init__(self, name: str) -> None:
        super().__init__(name, 256)

    def write_unsigned(self, value: int) -> None:
        # Writes are ignored
        return

    def set_unsigned(self, value: int) -> None:
        '''Sets a value that can be read by a future `read_unsigned`.

        This takes effect immediately and is used to model a write from the
        MAI. This is used by the simulation environment to provide a value
        that is later read by `read_unsigned` and doesn't relate to instruction
        execution (e.g. in RTL the MAI will update this register when a new
        result is available. Note that we do still report the change until the
        next commit.
        '''
        assert 0 <= value < (1 << 256)
        self._value = value
        self._next_value = value
        self._pending_write = True

    def set_32bit_unsigned(self, value: int, index: int) -> None:
        '''Sets the 32-bit chunk at the given index to the unsigned value.
        The index 0 corresponds to bits [31:0], index 1 to bits [63:32],etc..
        '''
        assert 0 <= value < (1 << 32)
        assert 0 <= index < 8
        current = self.read_unsigned()
        mask = ((1 << 32) - 1) << (index * 32)
        new_value = (current & ~mask) | (value << (index * 32))
        assert 0 <= new_value < (1 << 256)
        self.set_unsigned(new_value)

    # TODO: Remove this function once RTL also generates traces. Without the RTL traces the
    # simulation detects a trace mismatch and aborts.
    def changes(self) -> List[ISPRChange]:
        return []


class MaiInputWSR(DumbISPR):
    def __init__(self, name: str) -> None:
        super().__init__(name, 256)

    def read_32bit_unsigned(self, index: int) -> int:
        assert 0 <= index < 8
        mask = (1 << 32) - 1
        return (self.read_unsigned() >> (32 * index)) & mask

    # TODO: Remove this function once RTL also generates traces. Without the RTL traces the
    # simulation detects a trace mismatch and aborts.
    def changes(self) -> List[ISPRChange]:
        return []
