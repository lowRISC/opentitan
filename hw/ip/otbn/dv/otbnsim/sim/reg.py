# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Set

from .trace import Trace


class TraceRegister(Trace):
    def __init__(self, name: str, width: int, new_value: int):
        self.name = name
        self.width = width
        self.new_value = new_value

    def trace(self) -> str:
        fmt_str = '{{}} = 0x{{:0{}x}}'.format(self.width // 4)
        return fmt_str.format(self.name, self.new_value)

    def rtl_trace(self) -> str:
        return '> {}: {}'.format(self.name,
                                 Trace.hex_value(self.new_value, self.width))


class Reg:
    def __init__(self,
                 parent: Optional['RegFile'],
                 idx: int,
                 width: int,
                 uval: int):
        assert 0 <= width
        assert 0 <= uval < (1 << width)

        self._parent = parent
        self._idx = idx
        self._width = width

        self._uval = uval
        self._next_uval = None  # type: Optional[int]

    def read_unsigned(self, backdoor: bool = False) -> int:
        return self._uval

    def write_unsigned(self, uval: int, backdoor: bool = False) -> None:
        assert 0 <= uval < (1 << self._width)
        self._next_uval = uval
        if not backdoor and self._parent is not None:
            self._parent.mark_written(self._idx)

    def read_next(self) -> Optional[int]:
        return self._next_uval

    def read_signed(self) -> int:
        uval = self.read_unsigned()
        return uval - (1 << self._width if uval >> (self._width - 1) else 0)

    def read_unsigned_inverted(self) -> int:
        '''Read value as an unsigned integer, but invert all bits'''
        return self.read_unsigned() ^ ((1 << self._width) - 1)

    def write_signed(self, ival: int) -> None:
        assert -(1 << (self._width - 1)) <= ival < (1 << (self._width - 1))
        uval = (1 << self._width) + ival if ival < 0 else ival
        self.write_unsigned(uval)

    def commit(self) -> None:
        if self._next_uval is not None:
            self._uval = self._next_uval
        self._next_uval = None

    def abort(self) -> None:
        self._next_uval = None


class RegFile:
    '''A base class for register files (used for both GPRs and WDRs).

    For GPRs, we override it (see gpr.py) to support our magic x0 and x1
    behaviour.

    '''
    def __init__(self,
                 name_pfx: str,
                 width: int,
                 depth: int):
        assert 0 <= width
        assert 0 <= depth

        self._name_pfx = name_pfx
        self._width = width
        self._registers = [Reg(self, i, width, 0) for i in range(depth)]
        self._pending_writes = set()  # type: Set[int]

    def mark_written(self, idx: int) -> None:
        '''Mark a register as having been written'''
        assert 0 <= idx < len(self._registers)
        self._pending_writes.add(idx)

    def get_reg(self, idx: int) -> Reg:
        assert 0 <= idx < len(self._registers)
        return self._registers[idx]

    def changes(self) -> List[TraceRegister]:
        ret = []
        for idx in sorted(self._pending_writes):
            assert 0 <= idx < len(self._registers)
            next_val = self.get_reg(idx).read_next()
            assert next_val is not None
            ret.append(TraceRegister('{}{:02}'.format(self._name_pfx, idx),
                                     self._width,
                                     next_val))
        return ret

    def commit(self) -> None:
        for idx in self._pending_writes:
            assert 0 <= idx < len(self._registers)
            self._registers[idx].commit()
        self._pending_writes.clear()

    def abort(self) -> None:
        for idx in self._pending_writes:
            assert 0 <= idx < len(self._registers)
            self._registers[idx].abort()
        self._pending_writes.clear()

    def peek_unsigned_values(self) -> List[int]:
        '''Get a list of the (unsigned) values of the registers'''
        return [reg.read_unsigned(backdoor=True) for reg in self._registers]
