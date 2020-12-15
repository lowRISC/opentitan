# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, cast

from .trace import Trace


class TraceFlags(Trace):
    def __init__(self, group: int, value: 'FlagReg'):
        self.group = group
        self.value = value

    def trace(self) -> str:
        return ('fg{} = {{C: {}, M: {}, L: {}, Z: {}}}'
                .format(self.group,
                        int(self.value.C),
                        int(self.value.M),
                        int(self.value.L),
                        int(self.value.Z)))

    def rtl_trace(self) -> str:
        return ('> FLAGS{}: {{C: {}, M: {}, L: {}, Z: {}}}'
                .format(self.group,
                        int(self.value.C),
                        int(self.value.M),
                        int(self.value.L),
                        int(self.value.Z)))


class FlagReg:
    FLAG_NAMES = ['C', 'M', 'L', 'Z']

    def __init__(self, C: bool, M: bool, L: bool, Z: bool):
        self.C = C
        self.M = M
        self.L = L
        self.Z = Z

        self._new_val = None  # type: Optional['FlagReg']

    def set_flags(self, other: 'FlagReg') -> None:
        self._new_val = other

    def get_by_name(self, flag_name: str) -> bool:
        assert flag_name in FlagReg.FLAG_NAMES
        return cast(bool, getattr(self, flag_name))

    def get_by_idx(self, flag_idx: int) -> bool:
        assert 0 <= flag_idx <= 3
        flag_name = FlagReg.FLAG_NAMES[flag_idx]
        return self.get_by_name(flag_name)

    def changes(self, group: int) -> List[TraceFlags]:
        return ([] if self._new_val is None
                else [TraceFlags(group, self._new_val)])

    def commit(self) -> None:
        if self._new_val is not None:
            for n in FlagReg.FLAG_NAMES:
                setattr(self, n, getattr(self._new_val, n))
        self._new_val = None

    def abort(self) -> None:
        self._new_val = None

    def read_unsigned(self) -> int:
        '''Return a 4-bit number with the flags as ZLMC'''
        return ((int(self.Z) << 3) |
                (int(self.L) << 2) |
                (int(self.M) << 1) |
                (int(self.C) << 0))

    def write_unsigned(self, value: int) -> None:
        '''Set flags using bottom 4 bits of the unsigned number, value'''
        assert 0 <= value
        self.set_flags(FlagReg.from_bits(value))

    @staticmethod
    def mlz_for_result(C: bool, result: int) -> 'FlagReg':
        '''Generate flags for the result of an operation.

        C is the value for the C flag. result is the wide-side result value
        that is used to generate M, L and Z.

        '''
        M = bool((result >> 255) & 1)
        L = bool(result & 1)
        Z = bool(result == 0)
        return FlagReg(C=C, M=M, L=L, Z=Z)

    @staticmethod
    def from_bits(value: int) -> 'FlagReg':
        assert 0 <= value
        C = bool((value >> 0) & 1)
        M = bool((value >> 1) & 1)
        L = bool((value >> 2) & 1)
        Z = bool((value >> 3) & 1)
        return FlagReg(C=C, M=M, L=L, Z=Z)


class FlagGroups:
    def __init__(self) -> None:
        self._groups = {0: FlagReg(False, False, False, False),
                        1: FlagReg(False, False, False, False)}
        # Have any flags changed?
        self._dirty = False

    def __getitem__(self, key: int) -> FlagReg:
        assert 0 <= key <= 1
        return self._groups[key]

    def __setitem__(self, key: int, value: FlagReg) -> None:
        assert 0 <= key <= 1
        self._dirty = True
        self._groups[key].set_flags(value)

    def changes(self) -> List[TraceFlags]:
        return self._groups[0].changes(0) + self._groups[1].changes(1)

    def commit(self) -> None:
        if self._dirty:
            self._groups[0].commit()
            self._groups[1].commit()
        self._dirty = False

    def abort(self) -> None:
        if self._dirty:
            self._groups[0].abort()
            self._groups[1].abort()
        self._dirty = False

    def read_unsigned(self) -> int:
        '''Return the flag groups as an unsigned value (as seen by CSRs)

        Format is defined in FlagReg, with group 0 as LSB.

        '''
        return ((self._groups[1].read_unsigned() << 4) |
                (self._groups[0].read_unsigned() << 0))

    def write_unsigned(self, value: int) -> None:
        '''Set the flag groups with an unsigned value, ignoring unused bits

        Format is defined in FlagReg, with group 0 as LSB.

        '''
        assert 0 <= value
        mask4 = (1 << 4) - 1
        self._dirty = True
        self._groups[0].write_unsigned((value >> 0) & mask4)
        self._groups[1].write_unsigned((value >> 4) & mask4)
