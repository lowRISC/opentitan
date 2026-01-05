# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Callable, Optional, Sequence
from .flags import FlagGroups
from .kmac import Kmac
from .trace import Trace
from .wsr import WSRFile


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


class CustomCSR(CSR):
    """CSR model with optional per-instance read/write overrides."""

    def __init__(
        self,
        name: str,
        read_func: Optional[Callable[['CustomCSR'], int]] = None,
        write_func: Optional[Callable[['CustomCSR', int], None]] = None,
    ) -> None:
        super().__init__(name)
        # Store the callbacks as attributes.
        self._custom_read = read_func
        self._custom_write = write_func

    def read_unsigned(self) -> int:
        # If a custom function exists, call it.
        if self._custom_read:
            return self._custom_read(self)
        # TODO: Ignore reads if None
        # Otherwise, use the parent logic.
        return super().read_unsigned()

    def write_unsigned(self, value: int) -> None:
        # If a custom function exists, call it.
        if self._custom_write:
            self._custom_write(self, value)
        # TODO: Ignore writes if None
        # Otherwise, use the parent logic.
        else:
            super().write_unsigned(value)


class CSRFile:
    '''A model of the CSR file'''
    def __init__(self, kmac: Kmac) -> None:
        self.flags = FlagGroups()
        self.KMAC_STATUS = CustomCSR(
            name='KMAC_STATUS',
            read_func=lambda csr_self: kmac.get_status(),
            write_func=None
        )
        self.KMAC_IF_STATUS = CustomCSR(
            name='KMAC_IF_STATUS',
            read_func=lambda csr_self: kmac.get_if_status(),
            write_func=lambda csr_self, val: kmac.set_if_status(val),
        )
        self.KMAC_INTR = CustomCSR(
            name='KMAC_INTR',
            read_func=lambda csr_self: kmac.get_intr(),
            write_func=lambda csr_self, val: kmac.set_intr(val),
        )
        self.KMAC_ERROR = CustomCSR(
            name='KMAC_ERROR',
            read_func=lambda csr_self: kmac.get_error(),
            write_func=None,
        )
        self.KMAC_CFG = CustomCSR(
            name='KMAC_CFG',
            read_func=lambda csr_self: kmac.get_cfg(),
            write_func=lambda csr_self, val: kmac.set_cfg(val),
        )
        self.KMAC_MSG_SEND = CustomCSR(
            name='KMAC_MSG_SEND',
            read_func=None,
            write_func=lambda csr_self, val: kmac.set_msg_send(),
        )
        self.KMAC_CMD = CustomCSR(
            name='KMAC_CMD',
            read_func=None,
            write_func=lambda csr_self, val: kmac.set_cmd(val),
        )
        self.KMAC_BYTE_STROBE = CustomCSR(
            name='KMAC_BYTE_STROBE',
            read_func=lambda csr_self: kmac.get_strobe(),
            write_func=lambda csr_self, val: kmac.set_strobe(val)
        )

        self._known_indices = {
            0x7c0,  # FG0
            0x7c1,  # FG1
            0x7c8,  # FLAGS
            *range(0x7d0, 0x7d8),  # MODi
            0x7d8,  # RND_PREFETCH
            0x7e0,  # KMAC_STATUS
            0x7e1,  # KMAC_IF_STATUS
            0x7e2,  # KMAC_INTR
            0x7e3,  # KMAC_ERROR
            0x7e4,  # KMAC_CFG
            0x7e5,  # KMAC_MSG_SEND
            0x7e6,  # KMAC_CMD
            0x7e7,  # KMAC_BYTE_STROBE
            0xfc0,  # RND
            0xfc1,  # URND
        }

        self._by_idx = {
            0x7e0: self.KMAC_STATUS,
            0x7e1: self.KMAC_IF_STATUS,
            0x7e2: self.KMAC_INTR,
            0x7e3: self.KMAC_ERROR,
            0x7e4: self.KMAC_CFG,
            0x7e5: self.KMAC_MSG_SEND,
            0x7e6: self.KMAC_CMD,
            0x7e7: self.KMAC_BYTE_STROBE,
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

        if 0x7e0 <= idx <= 0x7e7:
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

        if 0x7e0 <= idx <= 0x7e7:
            # Write to KMAC register.
            return self._by_idx[idx].write_unsigned(value)

        if idx == 0xfc0:
            # RND register (which ignores writes)
            return

        if idx == 0xfc1:
            # URND register (which ignores writes)
            return

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def wipe(self) -> None:
        self.flags.write_unsigned(0)
