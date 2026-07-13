# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
from typing import Optional
from .ispr import DumbISPR


class MaiOperation(IntEnum):
    A2B = 11
    B2A = 16
    SECADD = 23
    SECADDMOD = 12


class MaiCtrlCSR(DumbISPR):
    '''Models the MAI CTRL CSR'''
    def __init__(self) -> None:
        self.START_BIT_MASK = 0x1
        self.START_BIT_OFFSET = 0
        self.OPERATION_MASK = 0x1f
        self.OPERATION_OFFSET = 1
        super().__init__("MAI_CTRL", 32)
        self.on_start()

    def on_start(self) -> None:
        super().on_start()
        # On start, the default operation is set.
        self._operation = MaiOperation.A2B
        self._raw_op: int = int(MaiOperation.A2B)
        self._start_bit = False
        self._value = self._get_value()

    def _construct_value(self, start_bit: bool, raw_op: int) -> int:
        '''Construct a register value from raw op bits and a start bit.'''
        raw = (((raw_op & self.OPERATION_MASK) << self.OPERATION_OFFSET) |
               (int(start_bit) << self.START_BIT_OFFSET))
        assert 0 <= raw < (1 << self.width)
        return raw

    def _get_value(self) -> int:
        '''Construct the register value based on the current raw op bits and start bit.'''
        return self._construct_value(self._start_bit, self._raw_op)

    def _extract_start_bit(self, value: int) -> bool:
        '''Extract the start bit from a register value.'''
        return ((value >> self.START_BIT_OFFSET) & self.START_BIT_MASK) != 0

    def _extract_operation(self, value: int) -> MaiOperation:
        '''Extract the operation field from a register value.
        The value to be checked must specify a valid operation option otherwise we crash.'''
        # If the conversion failed, the check when updating the operation did fail already.
        return MaiOperation((value >> self.OPERATION_OFFSET) & self.OPERATION_MASK)

    def _extract_raw_op(self, value: int) -> int:
        '''Extract the raw (possibly invalid) operation bits from a register value.'''
        return (value >> self.OPERATION_OFFSET) & self.OPERATION_MASK

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
        self._pending_write = False

    def commit(self) -> None:
        if self._next_value is not None:
            self._start_bit = self._extract_start_bit(self._next_value)
            self._raw_op = self._extract_raw_op(self._next_value)
            try:
                self._operation = MaiOperation(self._raw_op)
            except ValueError:
                pass  # keep _operation as the last valid MaiOperation
            self._value = self._next_value
        self._next_value = None
        self._pending_write = False

    def has_reserved_bits(self, value: int) -> bool:
        '''Return True if value has any bits set outside the defined [5:0] field.

        Mirrors RTL ispr_mai_sw_err.rsvd_csr_write: any write with bits [31:6] non-zero.
        '''
        valid_mask = (self.OPERATION_MASK << self.OPERATION_OFFSET) | self.START_BIT_MASK
        return bool(value & ~valid_mask & 0xFFFFFFFF)

    def is_raw_op_valid(self, value: int) -> bool:
        '''Return True if the op field of `value` is a valid MAI operation.
        '''
        return self.is_valid_operation(value)

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

    def would_change_raw_op(self, value: int) -> bool:
        '''Return whether writing value would change the op field (compares raw bits).

        Safe to call with any value, including those with invalid op encodings.
        '''
        return self._extract_raw_op(value) != self._raw_op


class MaiStatusCSR(DumbISPR):
    '''Models the MAI STATUS CSR'''
    def __init__(self) -> None:
        self.BUSY_BIT_OFFSET = 0
        self.INPUT_READY_BIT_OFFSET = 1
        super().__init__("MAI_STATUS", 32)
        self.on_start()

    def on_start(self) -> None:
        super().on_start()
        # On start, the MAI is not busy and is ready for new inputs.
        self._is_busy = False
        self._is_input_ready = True
        self._value = self._get_value()

    def write_unsigned(self, value: int) -> None:
        '''Ignore writes to the MAI STATUS CSR.

        Note this is different from update_ methods. This is used by instructions and the update_
        methods are used directly by the MAI hardware.'''
        return

    def _get_value(self) -> int:
        '''Construct the register value based on the current busy and input-ready bits.'''
        return ((self._is_busy << self.BUSY_BIT_OFFSET) |
                (self._is_input_ready << self.INPUT_READY_BIT_OFFSET))

    def _update_bits(self,
                     busy: Optional[bool] = None,
                     input_ready: Optional[bool] = None) -> None:
        '''Set or clear the busy and input-ready bits in the CSR based on the provided values.

        This takes effect immediately. Note that we still report the change to generate a proper
        trace.'''
        if busy is not None:
            self._is_busy = busy
        if input_ready is not None:
            self._is_input_ready = input_ready
        self._value = self._get_value()
        self._next_value = self._get_value()
        self._pending_write = False

    def is_input_ready(self) -> bool:
        return self._is_input_ready

    def update_input_ready_bit(self, input_ready: bool) -> None:
        self._update_bits(input_ready=input_ready)

    def is_busy(self) -> bool:
        return self._is_busy

    def update_busy_bit(self, busy: bool) -> None:
        self._update_bits(busy=busy)


class MaiOutputWSR(DumbISPR):
    def __init__(self, name: str) -> None:
        super().__init__(name, 256)

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
        self._pending_write = False

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


class MaiInputWSR(DumbISPR):
    def __init__(self, name: str) -> None:
        super().__init__(name, 256)

    def read_32bit_unsigned(self, index: int) -> int:
        assert 0 <= index < 8
        mask = (1 << 32) - 1
        return (self.read_unsigned() >> (32 * index)) & mask
