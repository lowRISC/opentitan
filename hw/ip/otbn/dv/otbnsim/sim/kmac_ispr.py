# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List
from .ispr import ISPR, DumbISPR, ISPRChange


class KmacCommandCSR(DumbISPR):
    '''Models a KMAC command CSR where the command is cleared one cycle after it has been issued.'''

    def __init__(self, name: str, write_mask: int):
        super().__init__(name, 32)
        self.write_mask = write_mask

    def write_unsigned(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value & self.write_mask)

    def commit(self) -> None:
        self._pending_write = False

        # In case of a write, commit the next state.
        if self._next_value is not None:
            self._value = self._next_value
            # If we are writing a command, it needs to be cleared in the next cycle.
            if self._next_value != 0:
                self._next_value = 0
                self._pending_write = True
            # Clear the state after the command has been issued.
            else:
                self._next_value = None

    def abort(self) -> None:
        self._next_value = None
        self._pending_write = False
        self._value = 0

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    # Without this override, changes will be handled by the super-class.
    def changes(self) -> List[ISPRChange]:
        return []


class KmacMirrorCSR(DumbISPR):
    '''Models a KMAC CSR which mirrors the CSR in the KMAC HWIP.'''

    def __init__(self, name: str):
        super().__init__(name, 32)

    def write_unsigned(self, value: int) -> None:
        # Writes from software are explicitly ignored as this is a Read-Only mirror.
        return

    def update_from_hw(self, value: int) -> None:
        # Updates the register value from the Hardware side.
        # This uses the superclass logic to stage the value as a pending write.
        super().write_unsigned(value)

    def abort(self) -> None:
        # Since this CSR is read only for SW, HW is the only one writing to this register.
        # Therefore, all writes are always committed (even on aborts).
        self.commit()

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    # Without this override, changes will be handled by the super-class.
    def changes(self) -> List[ISPRChange]:
        return []


class KmacStatusCSR(KmacMirrorCSR):
    '''Models the KMAC_STATUS CSR.'''

    def set_idle(self) -> None:
        self.update_from_hw(1)

    def is_idle(self) -> bool:
        return bool(self.read_unsigned() & 0x1)

    def set_absorb(self) -> None:
        self.update_from_hw(2)

    def is_absorbing(self) -> bool:
        return bool((self.read_unsigned() >> 1) & 0x1)

    def set_squeeze(self) -> None:
        self.update_from_hw(4)

    def is_squeezing(self) -> bool:
        return bool((self.read_unsigned() >> 2) & 0x1)


class KmacErrorCSR(KmacMirrorCSR):
    '''Models the KMAC_ERROR CSR.'''

    def write_error(self, value: int) -> None:
        assert 0 <= value < (1 << self.width)
        super().update_from_hw(value & 0xff)


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
    # Without this override, changes will be handled by the super-class.
    def changes(self) -> List[ISPRChange]:
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
        self.clr_bits(value & self._clearable_mask)

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

    def clr_bits(self, mask: int) -> None:
        assert 0 <= mask < self.width
        self._clr_mask |= mask
        self._pending_write |= (mask != 0)

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
    # Without this override, changes will be handled by the super-class.
    def changes(self) -> List[ISPRChange]:
        return []


class KmacIfStatusCSR(KmacSetClrCSR):
    '''Models the KMAC_IF_STATUS CSR.'''
    # Bit field positions.
    MSG_WRITE_RDY_POS: int = 0
    MSG_SEND_ERROR_POS: int = 1
    MSG_WRITE_ERROR_POS: int = 2
    DIGEST_VALID_POS: int = 3

    # Bits that Software is allowed to clear (e.g., MSG_SEND_ERROR_POS, MSG_WRITE_ERROR_POS)
    CLEARABLE_MASK: int = (1 << MSG_SEND_ERROR_POS) | (1 << MSG_WRITE_ERROR_POS)

    def __init__(self, name: str):
        super().__init__(name, self.CLEARABLE_MASK)

    def clr_msg_send_error(self) -> None:
        self.clr_bit(self.MSG_SEND_ERROR_POS)

    def clr_msg_write_error(self) -> None:
        self.clr_bit(self.MSG_WRITE_ERROR_POS)

    def clr_digest_valid(self) -> None:
        # Clears the DIGEST_VALID bit immediately.
        # Note: This creates a 0-cycle delay relative to the function call to
        # compensate for the Kmac() model detecting reads 1 cycle late.
        clr_mask = (1 << self.DIGEST_VALID_POS)
        self._value &= ~clr_mask

    def get_msg_write_rdy(self) -> bool:
        return self.get_bit(self.MSG_WRITE_RDY_POS)

    def get_msg_send_error(self) -> bool:
        return self.get_bit(self.MSG_SEND_ERROR_POS)

    def get_msg_write_error(self) -> bool:
        return self.get_bit(self.MSG_WRITE_ERROR_POS)

    def get_digest_valid(self) -> bool:
        return self.get_bit(self.DIGEST_VALID_POS)

    def set_msg_send_error(self) -> None:
        self.set_bit(self.MSG_SEND_ERROR_POS)

    def set_msg_write_error(self) -> None:
        self.set_bit(self.MSG_WRITE_ERROR_POS)

    def set_digest_valid(self) -> None:
        self.set_bit(self.DIGEST_VALID_POS)

    def update_msg_write_rdy(self, value: bool = True) -> None:
        # Update the msg_write_rdy bit to "value"
        if value:
            self.set_bit(self.MSG_WRITE_RDY_POS)
        else:
            self.clr_bit(self.MSG_WRITE_RDY_POS)


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
    '''Models a single KMAC_DATA_S0/1 WSR.

    This class handles the logic for abortable vs non-abortable writes.
    '''
    def __init__(self, name: str):
        super().__init__(name, 256)
        self._is_abortable_write = True

    def on_start(self) -> None:
        super().on_start()
        self._is_abortable_write = True

    def write_unsigned(self, value: int, abortable: bool = False) -> None:
        assert 0 <= value < (1 << self.width)
        super().write_unsigned(value)
        self._is_abortable_write = abortable

    def commit(self) -> None:
        super().commit()
        self._is_abortable_write = True

    def abort(self) -> None:
        # Abort the pending write if allowed, otherwise commit it.
        if self._is_abortable_write:
            super().abort()
        else:
            self.commit()

    # TODO: Remove this function once the kmac interface traces are needed for DV.
    # Without this override, changes will be handled by the super-class.
    def changes(self) -> List[ISPRChange]:
        return []


class KmacDataWSRs():
    """Models both of the KMAC_DATA_S0/1 WSRs and tracks their status."""
    def __init__(self, names: List[str]):
        self.shares: List[KmacDataWSR] = [KmacDataWSR(name) for name in names]
        self._read = [False] * len(self.shares)
        self._dirty = [False] * len(self.shares)

    def on_start(self) -> None:
        for share in self.shares:
            share.on_start()
        self.mark_all_unread()
        self.clean_shares()

    def all_shares_read(self) -> bool:
        return all(self._read)

    def mark_all_unread(self) -> None:
        self._read = [False] * len(self.shares)

    def shares_dirty(self) -> bool:
        return any(self._dirty)

    def clean_shares(self) -> None:
        self._dirty = [False] * len(self.shares)

    def read_unsigned(self, share_idx: int) -> int:
        if 0 <= share_idx < len(self.shares):
            self._read[share_idx] = True
            return self.shares[share_idx].read_unsigned()
        raise IndexError(f"Share index {share_idx} out of range")

    def get_unsigned(self, share_idx: int) -> int:
        # Read without marking as read (peeking).
        return self.shares[share_idx].read_unsigned()

    def set_unsigned(self, value: int, share_idx: int = 0) -> None:
        # Write to a share without marking it dirty (e.g., backdoor load).
        self.shares[share_idx].write_unsigned(value, abortable=False)

    def write_unsigned(self, value: int, share_idx: int = 0) -> None:
        # Write to a share, marking it dirty and abortable.
        if 0 <= share_idx < len(self.shares):
            self._dirty[share_idx] = True
            self.shares[share_idx].write_unsigned(value, abortable=True)
        else:
            raise IndexError(f"Share index {share_idx} out of range")

    def commit(self) -> None:
        for share in self.shares:
            share.commit()

    def abort(self) -> None:
        for share in self.shares:
            share.abort()

    def changes(self) -> List[ISPRChange]:
        ret: List[ISPRChange] = []
        for share in self.shares:
            ret += share.changes()
        return ret
