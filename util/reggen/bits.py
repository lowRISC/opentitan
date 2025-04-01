# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Support code for bit ranges in reggen'''

from typing import Tuple

from reggen.lib import check_str
from reggen.params import ReggenParams


class Bits:

    def __init__(self, msb: int, lsb: int):
        assert 0 <= lsb <= msb
        self.msb = msb
        self.lsb = lsb

    def bitmask(self) -> int:
        return (1 << (self.msb + 1)) - (1 << self.lsb)

    def width(self) -> int:
        return 1 + self.msb - self.lsb

    def max_value(self) -> int:
        return (1 << self.width()) - 1

    def extract_field(self, reg_val: int) -> int:
        return (reg_val & self.bitmask()) >> self.lsb

    @staticmethod
    def from_raw(where: str, reg_width: int, params: ReggenParams,
                 raw: object) -> 'Bits':
        # Bits should be specified as msb:lsb or as just a single bit index.
        if isinstance(raw, int):
            msb = raw
            lsb = raw
        else:
            str_val = check_str(raw, 'bits field for {}'.format(where))
            msb, lsb = Bits._parse_str(where, params, str_val)

        # Check that the bit indices look sensible
        if msb < lsb:
            raise ValueError(
                f'msb for {where} is {msb}: less than {lsb}, the lsb.')
        if lsb < 0:
            raise ValueError(f'lsb for {where} is {lsb}, which is negative.')
        if msb >= reg_width:
            raise ValueError(f"msb for {where} is {msb}, which doesn't fit in "
                             f"{reg_width} bits.")

        return Bits(msb, lsb)

    @staticmethod
    def _parse_str(where: str, params: ReggenParams,
                   str_val: str) -> Tuple[int, int]:
        try:
            idx = int(str_val)
            return (idx, idx)
        except ValueError:
            # Doesn't look like an integer. Never mind: try msb:lsb
            pass

        parts = str_val.split(':')
        if len(parts) != 2:
            raise ValueError(
                f'bits field for {where} is not an integer or of the form '
                f'msb:lsb. Saw {str_val!r}.')
        return (params.expand(parts[0], f'msb of bits field for {where}'),
                params.expand(parts[1], f'lsb of bits field for {where}'))

    def make_translated(self, bit_offset: int) -> 'Bits':
        assert 0 <= bit_offset
        return Bits(self.msb + bit_offset, self.lsb + bit_offset)

    def as_str(self) -> str:
        if self.lsb == self.msb:
            return str(self.lsb)
        else:
            assert self.lsb < self.msb
            return '{}:{}'.format(self.msb, self.lsb)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Bits):
            return NotImplemented
        return (self.lsb == other.lsb) and (self.msb == other.msb)

    def __str__(self) -> str:
        return '[{}:{}]'.format(self.msb, self.lsb)
