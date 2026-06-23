# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional
from .ispr import ISPR, DumbISPR, ISPRChange


class KmacStatusCSR(ISPR):

    READY_POS = 0
    RSP_VALID_POS = 1
    RSP_ERROR_POS = 2
    CTRL_ERROR_POS = 3
    MSG_WRITE_ERROR_POS = 4

    W1C_MASK = ((1 << CTRL_ERROR_POS) |
                (1 << MSG_WRITE_ERROR_POS) |
                (1 << RSP_ERROR_POS))

    # All implemented status bits [4:0].
    VALUE_MASK = ((1 << READY_POS) |
                  (1 << RSP_VALID_POS) |
                  (1 << RSP_ERROR_POS) |
                  (1 << CTRL_ERROR_POS) |
                  (1 << MSG_WRITE_ERROR_POS))

    def __init__(self, name: str):
        super().__init__(name, 32)
        self._value = 0
        self._set_mask = 0
        self._clr_mask = 0

    def on_start(self) -> None:
        self._value = 0
        self._set_mask = 0
        self._clr_mask = 0

    def read_unsigned(self) -> int:
        return self._value

    def write_unsigned(self, value: int) -> None:
        # SW writes are W1C.
        self._clr_mask |= value & self.W1C_MASK

    def _hw_set_bit(self, bit: int, value: bool) -> None:
        # Immediately update the selected bit.
        if value:
            self._value |= (1 << bit)
        else:
            self._value &= ~(1 << bit)

    def hw_set_ready(self, value: bool) -> None:
        self._hw_set_bit(self.READY_POS, value)

    def hw_set_rsp_valid(self, value: bool) -> None:
        self._hw_set_bit(self.RSP_VALID_POS, value)

    def hw_write_error(self, bit: int) -> None:
        # Stage a sticky error bit. Revealed to SW once instruction ends independently of whether
        # the instruction commits or aborts.
        self._set_mask |= (1 << bit)

    def hw_set_rsp_error(self) -> None:
        self.hw_write_error(self.RSP_ERROR_POS)

    def hw_set_ctrl_error(self) -> None:
        self.hw_write_error(self.CTRL_ERROR_POS)

    def hw_set_msg_write_error(self) -> None:
        self.hw_write_error(self.MSG_WRITE_ERROR_POS)

    def hw_clr_error_bits(self) -> None:
        error_mask = ((1 << self.RSP_ERROR_POS) |
                      (1 << self.CTRL_ERROR_POS) |
                      (1 << self.MSG_WRITE_ERROR_POS))
        self._value &= ~error_mask

    def commit(self) -> None:
        # Apply the staged SW W1C clear and the staged HW set. Setting a bit has priority over
        # clearing it.
        self._value = ((self._value & ~self._clr_mask) | self._set_mask) & self.VALUE_MASK
        self._set_mask = 0
        self._clr_mask = 0

    def abort(self) -> None:
        # Abort the insn execution which means discarding any W1C. Hardware updates always commit.
        self._value = (self._value | self._set_mask) & self.VALUE_MASK
        self._set_mask = 0
        self._clr_mask = 0

    def changes(self) -> List[ISPRChange]:
        # Do not emit a trace because reads are not traced, only SW writes are. But this is read
        # only.
        return []


class KmacCtrlCSR(ISPR):
    '''Models the KMAC_CTRL CSR.

    Bit layout:
      [4:0]   command bits START/SEND/PROCESS/DONE/CLOSE
      [31:5]  reserved

    KMAC_CTRL only issues commands and always reads as 0.
    '''

    CMD_MASK = 0x1f

    def __init__(self, name: str):
        super().__init__(name, 32)
        self._cmd = 0
        self._cmd_next: Optional[int] = None
        # Full 32-bit value of a SW write, required for tracing.
        self._write_value = 0
        self._pending_write = False

    def on_start(self) -> None:
        self._cmd = 0
        self._cmd_next = None
        self._write_value = 0
        self._pending_write = False

    def read_unsigned(self) -> int:
        # Cmd bits always read back as 0.
        return 0

    def write_unsigned(self, value: int) -> None:
        # Keep the full written value for tracing.
        self._write_value = value & ((1 << self.width) - 1)
        self._cmd_next = value & self.CMD_MASK
        self._pending_write = True

    def take_cmd(self) -> int:
        '''Read and clear the current command. Must be called before the next insn executes.'''
        cmd = self._cmd
        self._cmd = 0
        return cmd

    def peek_pending_cmd(self) -> int:
        '''Return the command staged by the current insn (0 if none). To be used after the current
        insn executed.'''
        return self._cmd_next if self._cmd_next is not None else 0

    def wipe(self) -> None:
        self._cmd = 0
        self._cmd_next = None
        self._write_value = 0
        self._pending_write = False

    def commit(self) -> None:
        if self._cmd_next is not None:
            self._cmd = self._cmd_next
            self._cmd_next = None
        self._pending_write = False

    def abort(self) -> None:
        self._cmd_next = None
        self._pending_write = False

    def changes(self) -> List[ISPRChange]:
        if self._pending_write:
            return [ISPRChange(self.name, self.width, self._write_value)]
        return []


class KmacCfgCSR(ISPR):
    '''Models the KMAC_CFG CSR.

    Bit layout:
      [0]     EN_XOF
      [3:1]   STRENGTH
      [5:4]   MODE
      [15:6]  reserved
      [16]    EN_XOF_INV
      [19:17] STRENGTH_INV
      [21:20] MODE_INV
      [31:22] reserved

    The _INV fields must hold the bitwise inverted value of their lower
    counterparts for the configuration to be valid.
    '''

    CFG_MASK = 0x3f003f  # lower fields [5:0] and inverted fields [21:16]

    def __init__(self, name: str):
        super().__init__(name, 32)
        self._cfg = 0
        self._cfg_next: Optional[int] = None
        # Full 32-bit value of a SW write, required for tracing.
        self._write_value = 0
        self._written_this_cycle = False
        self._pending_write = False

    def on_start(self) -> None:
        self._cfg = 0
        self._cfg_next = None
        self._write_value = 0
        self._written_this_cycle = False
        self._pending_write = False

    def read_unsigned(self) -> int:
        return self._cfg & self.CFG_MASK

    def write_unsigned(self, value: int) -> None:
        # Keep the full written value for tracing.
        self._write_value = value & ((1 << self.width) - 1)
        self._cfg_next = value & self.CFG_MASK
        self._written_this_cycle = True
        self._pending_write = True

    def get_en_xof(self) -> bool:
        return bool(self._cfg & 0x1)

    def get_strength(self) -> int:
        return (self._cfg >> 1) & 0x7

    def get_mode(self) -> int:
        return (self._cfg >> 4) & 0x3

    def get_en_xof_inv(self) -> int:
        return (self._cfg >> 16) & 0x1

    def get_strength_inv(self) -> int:
        return (self._cfg >> 17) & 0x7

    def get_mode_inv(self) -> int:
        return (self._cfg >> 20) & 0x3

    def redundancy_valid(self) -> bool:
        '''Check that the _INV fields are the bitwise inverse of the lower fields.
        Note, this check is actually performed on the KMAC side, not by OTBN. For simulation
        reasons it is implemented here.'''
        en_xof_ok = self.get_en_xof_inv() == (~int(self.get_en_xof()) & 0x1)
        strength_ok = self.get_strength_inv() == (~self.get_strength() & 0x7)
        mode_ok = self.get_mode_inv() == (~self.get_mode() & 0x3)
        return en_xof_ok and strength_ok and mode_ok

    def is_written(self) -> bool:
        return self._written_this_cycle

    def wipe(self) -> None:
        self._cfg = 0
        self._cfg_next = None
        self._write_value = 0
        self._written_this_cycle = False
        self._pending_write = False

    def commit(self) -> None:
        if self._cfg_next is not None:
            self._cfg = self._cfg_next
            self._cfg_next = None
        self._pending_write = False
        self._written_this_cycle = False

    def abort(self) -> None:
        self._cfg_next = None
        self._pending_write = False
        self._written_this_cycle = False

    def changes(self) -> List[ISPRChange]:
        # The full write is traced despite only the config bits are stored.
        if self._pending_write:
            return [ISPRChange(self.name, self.width, self._write_value)]
        return []


class KmacStrbCSR(DumbISPR):
    '''Models the KMAC_STRB CSR.'''

    def __init__(self, name: str):
        super().__init__(name, 32)
        self._written_this_cycle = False

    def on_start(self) -> None:
        super().on_start()
        self._written_this_cycle = False

    def write_unsigned(self, value: int) -> None:
        super().write_unsigned(value)
        self._written_this_cycle = True

    def is_written(self) -> bool:
        return self._written_this_cycle

    def commit(self) -> None:
        super().commit()
        self._written_this_cycle = False

    def abort(self) -> None:
        super().abort()
        self._written_this_cycle = False


class KmacDataWSR(DumbISPR):
    '''Models one KMAC_DATA_S0 / KMAC_DATA_S1 WSR.

    Written by SW (256-bit, abortable) or by the HW when a digest response arrives. A digest
    response only updates the lowest 64 bits. A HW write is non-abortable and has priority over a
    SW write. A SW read returns the full WSR.'''

    HW_WRITE_BITS = 64
    HW_WRITE_MASK = (1 << HW_WRITE_BITS) - 1

    def __init__(self, name: str):
        super().__init__(name, 256)
        self._hw_value: Optional[int] = None
        self._written_this_cycle = False
        self._read = False

    def on_start(self) -> None:
        super().on_start()
        self._hw_value = None
        self._written_this_cycle = False
        self._read = False

    def write_unsigned(self, value: int) -> None:
        # Used by SW writes and is abortable.
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value)
        self._written_this_cycle = True

    def read_unsigned(self) -> int:
        self._read = True
        return self._value

    def hw_write(self, value: int) -> None:
        # A HW digest response writes only the lowest 64 bits, is non-abortable and not traced.
        assert 0 <= value < (1 << self.HW_WRITE_BITS)
        self._hw_value = value

    def get_unsigned(self) -> int:
        return self._value

    def is_written(self) -> bool:
        # A SW write occurred in this cycle. Flag is cleared when change is committed.
        return self._written_this_cycle

    def is_hw_written(self) -> bool:
        # A HW write occurred in this cycle.
        return self._hw_value is not None

    def was_read(self) -> bool:
        return self._read

    def clr_read(self) -> None:
        self._read = False

    def commit(self) -> None:
        # A SW write updates all words. A HW digest response writes to the lowest 64 bits.
        self._value = self._next_value if self._next_value is not None else self._value
        if self._hw_value is not None:
            self._value = (self._value & ~self.HW_WRITE_MASK) | self._hw_value
        self._next_value = None
        self._pending_write = False
        self._hw_value = None
        self._written_this_cycle = False

    def abort(self) -> None:
        # The SW write is discarded, but a HW digest response is non-abortable.
        if self._hw_value is not None:
            self._value = (self._value & ~self.HW_WRITE_MASK) | self._hw_value
        self._next_value = None
        self._pending_write = False
        self._hw_value = None
        self._written_this_cycle = False
