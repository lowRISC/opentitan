# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import List, Tuple


class BitRanges:
    '''Represents the bit ranges used for a field in an encoding scheme'''
    def __init__(self,
                 mask: int,
                 ranges: List[Tuple[int, int]],
                 width: int) -> None:
        self.mask = mask
        self.ranges = ranges
        self.width = width

    @staticmethod
    def from_list(ranges: List[Tuple[int, int]]) -> 'BitRanges':
        mask = 0
        width = 0
        for msb, lsb in ranges:
            assert 0 <= lsb <= msb <= 31
            rng_mask = (1 << (msb + 1)) - (1 << lsb)
            assert not (rng_mask & mask)
            mask |= rng_mask
            width += msb - lsb + 1

        return BitRanges(mask, ranges, width)

    @staticmethod
    def from_yaml(as_string: str, what: str) -> 'BitRanges':
        #   ranges ::= range
        #            | range ',' ranges
        #
        #   range ::= num
        #           | num ':' num
        #
        # Ranges are assumed to be msb:lsb (with msb >= lsb). Bit indices are
        # at most 31 and ranges are disjoint.

        if not as_string:
            raise ValueError('Empty string as bits for {}'.format(what))

        overlaps = 0

        mask = 0
        ranges = []
        width = 0

        for rng in as_string.split(','):
            match = re.match(r'([0-9]+)(?:-([0-9]+))?$', rng)
            if match is None:
                raise ValueError('Range {!r} in bits for {} is malformed.'
                                 .format(rng, what))

            msb = int(match.group(1))
            maybe_lsb = match.group(2)
            lsb = msb if maybe_lsb is None else int(maybe_lsb)

            if msb < lsb:
                raise ValueError('Range {!r} in bits for {} has msb < lsb.'
                                 .format(rng, what))

            if msb >= 32:
                raise ValueError('Range {!r} in bits for {} has msb >= 32.'
                                 .format(rng, what))

            rng_mask = (1 << (msb + 1)) - (1 << lsb)
            overlaps |= rng_mask & mask
            mask |= rng_mask

            ranges.append((msb, lsb))
            width += msb - lsb + 1

        if overlaps:
            raise ValueError('Bits for {} have overlapping ranges '
                             '(mask: {:#08x})'
                             .format(what, overlaps))

        return BitRanges(mask, ranges, width)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, BitRanges) and self.ranges == other.ranges

    def encode(self, value: int) -> int:
        '''Encode the given value as bit fields'''
        ret = 0
        bits_taken = 0
        for msb, lsb in self.ranges:
            rng_width = msb - lsb + 1
            value_msb = self.width - 1 - bits_taken
            value_lsb = value_msb - rng_width + 1

            rng_mask = (1 << rng_width) - 1
            rng_value = (value >> value_lsb) & rng_mask
            ret |= rng_value << lsb
            bits_taken += rng_width

        assert bits_taken == self.width
        return ret

    def decode(self, raw: int) -> int:
        '''Extract the bit fields from the given value'''
        ret = 0
        for msb, lsb in self.ranges:
            width = msb - lsb + 1
            mask = (1 << width) - 1

            ret <<= width
            ret |= (raw >> lsb) & mask
        return ret
