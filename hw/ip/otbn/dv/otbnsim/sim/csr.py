# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Any, Callable, Dict, List, Optional
from .flags import FlagGroups
from .ispr import DumbISPR
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
        self.RND = WrapperCSR(read_func=wsrs.RND.read_u32)
        self.URND = WrapperCSR(read_func=wsrs.URND.read_u32)

        self._known_indices = {
            0x7c0,  # FG0
            0x7c1,  # FG1
            0x7c8,  # FLAGS
            *range(0x7d0, 0x7d8),  # MODi
            0x7d8,  # RND_PREFETCH
            0xfc0,  # RND
            0xfc1,  # URND
        }

        self._idx_to_csr: Dict[int, Any] = {
            0x7c0: self.flags.groups[0],
            0x7c1: self.flags.groups[1],
            0x7c8: self.flags,
            0x7d8: self.RND_PREFETCH,
            0xfc0: self.RND,
            0xfc1: self.URND,
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
        if 0x7d0 <= idx <= 0x7d7:
            # MOD0 .. MOD7. MODi is bits [32*(i+1)-1..32*i]
            mod_n = idx - 0x7d0
            return self._get_field(mod_n, 32, wsrs.MOD.read_unsigned())

        csr = self._idx_to_csr.get(idx)
        if csr is not None:
            return int(csr.read_unsigned())

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

        raise RuntimeError('Unknown CSR index: {:#x}'.format(idx))

    def wipe(self) -> None:
        self.flags.write_unsigned(0)
