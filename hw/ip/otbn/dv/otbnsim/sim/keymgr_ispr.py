# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional
from .ispr import CtrlCSR, DumbISPR, ISPRChange


class KeymgrCtrlCSR(CtrlCSR):
    '''Models the KEYMGR_CTRL CSR.

    Bit layout:
      [0]    START
      [1]    SEND
      [2]    reserved
      [3]    SEND_ERROR
      [31:4] reserved
    '''

    CMD_MASK = 0xb


class KeymgrStatusCSR(DumbISPR):

    RECEIVING_POS = 0
    SENDING_POS = 1
    MSG_VALID_POS = 2
    MSG_COMPLETE_POS = 3

    STRB_WIDTH = 8
    STRB_OFFSET = 16

    def _stage_update(self, value: int, offset: int, width: int) -> None:
        assert 0 <= value < (1 << width)
        clear_mask = ~(((1 << width) - 1) << offset)

        base_value = self._value
        if self._pending_write and self._next_value is not None:
            base_value = self._next_value

        self._next_value = (base_value & clear_mask) | (value << offset)
        self._pending_write = True

    def _stage_bit(self, value: bool, bit: int) -> None:
        self._stage_update(value, bit, 1)

    def stage_receiving(self, receiving: bool) -> None:
        self._stage_bit(receiving, self.RECEIVING_POS)

    def stage_sending(self, sending: bool) -> None:
        self._stage_bit(sending, self.SENDING_POS)

    def stage_msg_valid(self, msg_valid: bool) -> None:
        self._stage_bit(msg_valid, self.MSG_VALID_POS)

    def stage_msg_complete(self, msg_complete: bool) -> None:
        self._stage_bit(msg_complete, self.MSG_COMPLETE_POS)

    def stage_strobe(self, strobe: int) -> None:
        self._stage_update(strobe, self.STRB_OFFSET, self.STRB_WIDTH)

    def set_msg_valid(self, msg_valid: bool) -> None:
        self._value = (self._value & ~(1 << self.MSG_VALID_POS)) | (
            (1 if msg_valid else 0) << self.MSG_VALID_POS)

    def msg_valid(self) -> bool:
        return bool((self._value >> self.MSG_VALID_POS) & 1)

    def write_unsigned(self, value: int) -> None:
        # This CSR ignores writes from SW.
        return

    def abort(self) -> None:
        # This CSR always commits.
        self.commit()

    def changes(self) -> List[ISPRChange]:
        # This CSR is read only.
        return []


class KeymgrMsgRcvWsr(DumbISPR):
    '''Models the WSR which receives the keymgr message.'''

    def on_start(self) -> None:
        self._value = 0
        self._next_value: Optional[int] = None
        self._pending_write = False
        self._value_sw: Optional[int] = None
        self._from_if: bool = False
        self._was_read: bool = False

    def read_unsigned(self) -> int:
        self._was_read = True
        return self._value

    def was_read(self) -> bool:
        '''Returns whether the previous instruction read this WSR. Then resets the flag.

        Must be read every cycle to keep flag up to date.'''
        was_read = self._was_read
        self._was_read = False
        return was_read

    def _write_unsigned(self, value: int, from_if: bool) -> None:
        assert 0 <= value < (1 << self.width)
        # An interface request has priority over a SW write. In the simulator, the interface
        # 'writes' before the insn executes. So ignore SW writes if a previous write is pending
        # but capture the value for tracing.
        if not from_if and self._pending_write:
            self._value_sw = value
            return
        self._from_if = from_if or self._from_if
        self._next_value = value
        self._pending_write = True

    def write_unsigned(self, value: int) -> None:
        self._write_unsigned(value, False)

    def stage_msg(self, msg: int) -> None:
        '''Capture a beat of the keymgr message.'''
        # This stages a write to the WSR at the end of the cycle. Any following SW write is
        # ignored. Any read still reads the old value.
        self._write_unsigned(msg, True)

    def write_invalid(self) -> None:
        super().write_invalid()
        self._value_sw = None

    def commit(self) -> None:
        super().commit()
        self._value_sw = None
        self._from_if = False

    def abort(self) -> None:
        if self._from_if:
            # Always commit a write from the interface.
            super().commit()
        else:
            super().abort()
        self._value_sw = None
        self._from_if = False

    def changes(self) -> List[ISPRChange]:
        # Only and always trace SW writes. Interface updates are not traced.
        trace_value = self._next_value

        # If there was a SW write simultaneously to a write from the interface trace the SW write.
        if self._value_sw is not None:
            trace_value = self._value_sw

        return ([ISPRChange(self.name, self.width, trace_value)]
                if self._pending_write else [])
