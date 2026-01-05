# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List
from .ispr import ISPR, DumbISPR, TraceISPR


class KmacCommandCSR(DumbISPR):
    '''Models a KMAC command CSR where the command is cleared one cycle after it has been issued.'''

    def __init__(self, name: str, write_mask: int):
        super().__init__(name, 32)
        self.write_mask = write_mask

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value & self.write_mask)

    def commit(self) -> None:
        # In case of a write commit the next state.
        if self._next_value is not None:
            self._value = self._next_value
            # In case we are writing a command it needs to be cleared in the next cycle.
            if self._next_value != 0:
                self._next_value = 0
                self._pending_write = True
            # Clear the state after the command has been issued.
            else:
                self._next_value = None
                self._pending_write = False

        # Default values in case we are neither writing nor clearing.
        else:
            self._next_value = None
            self._pending_write = False

    def abort(self) -> None:
        self._next_value = None
        self._pending_write = False
        self._value = 0

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    def changes(self) -> List[TraceISPR]:
        return []


class KmacCmdCSR(KmacCommandCSR):
    '''Models the KMAC_CMD CSR.'''

    def __init__(self, name: str):
        super().__init__(name, 0x3f)


class KmacMsgSemdCSR(KmacCommandCSR):
    '''Models the KMAC_MSG_SEND CSR.'''

    def __init__(self, name: str):
        super().__init__(name, 0x1)


class KmacMirrorCSR(DumbISPR):
    '''Models a KMAC CSR which mirrors the CSR in the KMAC HWIP.

    Since this CSR is read only for SW, HW is the only one writing to this register.
    Therefore, all writes are always committed (even on aborts).
    '''

    def __init__(self, name: str):
        super().__init__(name, 32)

    def abort(self) -> None:
        self.commit()

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    def changes(self) -> List[TraceISPR]:
        return []


class KmacStatusCSR(KmacMirrorCSR):
    '''Models the KMAC_STATUS CSR.'''

    def set_idle(self) -> None:
        self.write_unsigned(1)

    def is_idle(self) -> bool:
        return bool(self.read_unsigned() & 0x1)

    def set_absorb(self) -> None:
        self.write_unsigned(2)

    def is_absorbing(self) -> bool:
        return bool((self.read_unsigned() >> 1) & 0x1)

    def set_squeeze(self) -> None:
        self.write_unsigned(4)

    def is_squeezing(self) -> bool:
        return bool((self.read_unsigned() >> 2) & 0x1)


class KmacErrorCSR(KmacMirrorCSR):
    '''Models the KMAC_ERROR CSR.'''

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value & 0xff)


class KmacCfgCSR(DumbISPR):
    '''Models the KMAC_CFG CSR.'''

    def __init__(self, name: str):
        super().__init__(name, 32)

    def get_kmac_en(self) -> bool:
        return bool(self.read_unsigned() & 0x1)

    def get_kstrength(self) -> int:
        return (self.read_unsigned() >> 1) & 0x7

    def get_mode(self) -> int:
        return (self.read_unsigned() >> 4) & 0x3

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    def changes(self) -> List[TraceISPR]:
        return []


class KmacSetClrCSR(ISPR):
    '''Models a CSR where bits are set by HW and can be cleared by SW'''
    def __init__(self, name: str, clearable_mask: int):
        super().__init__(name, 32)
        self._value = 0
        self._clr_mask = 0
        self._set_mask = 0
        self._clearable_mask = clearable_mask

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)

        # Identify which bits we want to clear.
        bits_to_clear = value & self._clearable_mask

        if bits_to_clear != 0:
            # Clear the bits that SW wants to clear and is allowed to clear.
            for i in range(self.width):
                if (bits_to_clear >> i) & 1:
                    self.clr_bit(i)

    def on_start(self) -> None:
        self._value = 0
        self._clr_mask = 0
        self._set_mask = 0
        self._pending_write = False

    def read_unsigned(self) -> int:
        return self._value

    def clr_bit(self, pos: int) -> None:
        assert 0 <= pos < self.width
        self._clr_mask |= (1 << pos)
        self._pending_write = True

    def get_bit(self, pos: int) -> bool:
        assert 0 <= pos < self.width
        return bool((self._value >> pos) & 0x1)

    def set_bit(self, pos: int) -> None:
        assert 0 <= pos < self.width
        self._set_mask |= (1 << pos)
        self._pending_write = True

    def _get_next_value(self) -> int:
        # Set takes priority over clr.
        return (self._value & ~self._clr_mask) | self._set_mask

    def commit(self) -> None:
        self._value = self._get_next_value()
        self._clr_mask = 0
        self._set_mask = 0
        self._pending_write = False

    def abort(self) -> None:
        # Only reset the clear mask since SW doesn't set bits.
        self._clr_mask = 0
        self.commit()

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    def changes(self) -> List[TraceISPR]:
        return []


class KmacIfStatusCSR(KmacSetClrCSR):
    '''Models the KMAC_IF_STATUS CSR.'''
    # Bit field positions.
    MSG_WRITE_RDY_POS: int = 0
    MSG_SEND_ERROR_POS: int = 1
    MSG_WRITE_ERROR_POS: int = 2
    DIGEST_VALID_POS: int = 3

    # Bits that Software is allowed to clear (e.g., Error bits 1 and 2)
    CLEARABLE_MASK: int = (1 << MSG_SEND_ERROR_POS) | (1 << MSG_WRITE_ERROR_POS)

    def __init__(self, name: str):
        super().__init__(name, self.CLEARABLE_MASK)

    def clr_msg_write_rdy(self) -> None:
        self.clr_bit(self.MSG_WRITE_RDY_POS)

    def clr_msg_send_error(self) -> None:
        self.clr_bit(self.MSG_SEND_ERROR_POS)

    def clr_msg_write_error(self) -> None:
        self.clr_bit(self.MSG_WRITE_ERROR_POS)

    def clr_digest_valid(self) -> None:
        self.clr_bit(self.DIGEST_VALID_POS)

    def get_msg_write_rdy(self) -> bool:
        return self.get_bit(self.MSG_WRITE_RDY_POS)

    def get_msg_send_error(self) -> bool:
        return self.get_bit(self.MSG_SEND_ERROR_POS)

    def get_msg_write_error(self) -> bool:
        return self.get_bit(self.MSG_WRITE_ERROR_POS)

    def get_digest_valid(self) -> bool:
        return self.get_bit(self.DIGEST_VALID_POS)

    def set_msg_write_rdy(self) -> None:
        self.set_bit(self.MSG_WRITE_RDY_POS)

    def set_msg_send_error(self) -> None:
        self.set_bit(self.MSG_SEND_ERROR_POS)

    def set_msg_write_error(self) -> None:
        self.set_bit(self.MSG_WRITE_ERROR_POS)

    def set_digest_valid(self) -> None:
        self.set_bit(self.DIGEST_VALID_POS)


class KmacIntrCSR(KmacSetClrCSR):
    '''Models the KMAC_INTR CSR.'''
    # Bit field positions.
    ERROR_POS: int = 0

    # Bits that Software is allowed to clear (e.g., Error bit 0)
    CLEARABLE_MASK: int = (1 << ERROR_POS)

    def __init__(self, name: str):
        super().__init__(name, self.CLEARABLE_MASK)

    def clr_error(self) -> None:
        self.clr_bit(self.ERROR_POS)

    def get_error(self) -> bool:
        return self.get_bit(self.ERROR_POS)

    def set_error(self) -> None:
        self.set_bit(self.ERROR_POS)


class KmacDataWSR(DumbISPR):
    '''Models the KMAC_DATA_S0/1 WSRs.'''
    def __init__(self, name: str):
        super().__init__(name, 256)
        self._abortable = True

    def on_start(self) -> None:
        super().on_start()
        self._abortable = True

    def write_unsigned(self, value: int, abortable: bool = False) -> None:
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value)
        self._abortable = abortable

    def commit(self) -> None:
        super().commit()
        self._abortable = True

    def abort(self) -> None:
        if self._abortable:
            super().abort()
        else:
            self.commit()

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    def changes(self) -> List[TraceISPR]:
        return []
