# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for bit ranges in reggen'''

import re
from typing import List, Dict, Tuple

from .lib import check_str, expand_parameter


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
                 params: List[Dict[str, object]],
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
                   params: List[Dict[str, object]],
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
        return (Bits._parse_index('msb of bits field for {}'.format(where),
                                  params, parts[0]),
                Bits._parse_index('lsb of bits field for {}'.format(where),
                                  params, parts[1]))

    @staticmethod
    def _parse_index(where: str,
                     params: List[Dict[str, object]],
                     str_val: str) -> int:
        # Here, we want to support arithmetic expressions with + and -. We
        # don't support other operators, or parentheses (so can parse with just
        # a regex).
        #
        # Use re.split, capturing the operators. This turns e.g. "a + b-c" into
        # ['a ', '+', ' b', '-', 'c']. If there's a leading operator ("+a"),
        # the first element of the results is an empty string: elements with
        # odd positions are always operators and elements with even positions
        # are values.
        acc = 0
        is_neg = False

        for idx, tok in enumerate(re.split(r'([+-])', str_val)):
            if idx == 0 and not tok:
                continue
            if idx % 2:
                is_neg = (tok == '-')
                continue

            term = Bits._parse_value('term {} of {}'.format(idx // 2, where),
                                     params,
                                     tok.strip())
            acc += -term if is_neg else term

        return acc

    @staticmethod
    def _parse_value(where: str,
                     params: List[Dict[str, object]],
                     str_val: str) -> int:
        # If str_val is an integer, return it.
        try:
            return int(str_val)
        except ValueError:
            pass

        # Otherwise, search through params for a matching parameter.
        return expand_parameter(params, str_val,
                                'expanding {}'.format(where))

    def make_translated(self, bit_offset: int) -> 'Bits':
        assert 0 <= bit_offset
        return Bits(self.msb + bit_offset, self.lsb + bit_offset)

    def as_str(self) -> str:
        if self.lsb == self.msb:
            return str(self.lsb)
        else:
            assert self.lsb < self.msb
            return '{}:{}'.format(self.msb, self.lsb)
