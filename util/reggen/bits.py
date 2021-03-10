# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for bit ranges in reggen'''

from typing import Tuple

from .lib import check_str
from .params import ReggenParams


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
    def from_raw(where: str,
                 reg_width: int,
                 params: ReggenParams,
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
            raise ValueError('msb for {} is {}: less than {}, the msb.'
                             .format(where, msb, lsb))
        if lsb < 0:
            raise ValueError('lsb for {} is {}, which is negative.'
                             .format(where, lsb))
        if msb >= reg_width:
            raise ValueError("msb for {} is {}, which doesn't fit in {} bits."
                             .format(where, msb, reg_width))

        return Bits(msb, lsb)

    @staticmethod
    def _parse_str(where: str,
                   params: ReggenParams,
                   str_val: str) -> Tuple[int, int]:
        try:
            idx = int(str_val)
            return (idx, idx)
        except ValueError:
            # Doesn't look like an integer. Never mind: try msb:lsb
            pass

        parts = str_val.split(':')
        if len(parts) != 2:
            raise ValueError('bits field for {} is not an '
                             'integer or of the form msb:lsb. Saw {!r}.'
                             .format(where, str_val))
        return (params.expand(parts[0],
                              'msb of bits field for {}'.format(where)),
                params.expand(parts[1],
                              'lsb of bits field for {}'.format(where)))

    def make_translated(self, bit_offset: int) -> 'Bits':
        assert 0 <= bit_offset
        return Bits(self.msb + bit_offset, self.lsb + bit_offset)

    def as_str(self) -> str:
        if self.lsb == self.msb:
            return str(self.lsb)
        else:
            assert self.lsb < self.msb
            return '{}:{}'.format(self.msb, self.lsb)
