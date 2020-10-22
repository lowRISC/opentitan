# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


class BoolLiteral:
    '''Represents a boolean literal, with possible 'x characters

    We represent this as 2 masks: "ones" and "xs". The ones mask is the bits
    that are marked 1. The xs mask is the bits that are marked x. Then you can
    test whether a particular value matches the literal by zeroing all bits in
    the x mask and then comparing with the ones mask.

    '''
    def __init__(self, ones: int, xs: int, width: int) -> None:
        assert width > 0
        assert (ones >> width) == 0
        assert (xs >> width) == 0

        self.ones = ones
        self.xs = xs
        self.width = width

    @staticmethod
    def from_string(as_string: str, what: str) -> 'BoolLiteral':
        ones = 0
        xs = 0
        width = 0

        # The literal should always start with a 'b'
        if not as_string.startswith('b'):
            raise ValueError("Boolean literal for {} doesn't start with a 'b'."
                             .format(what))

        for char in as_string[1:]:
            if char == '_':
                continue

            ones <<= 1
            xs <<= 1
            width += 1

            if char == '0':
                continue
            elif char == '1':
                ones |= 1
            elif char == 'x':
                xs |= 1
            else:
                raise ValueError('Boolean literal for {} has '
                                 'unsupported character: {!r}.'
                                 .format(what, char))

        if not width:
            raise ValueError('Empty boolean literal for {}.'.format(what))

        return BoolLiteral(ones, xs, width)

    def char_for_bit(self, bit: int) -> str:
        '''Return 0, 1 or x for the bit at the given position'''
        assert bit < self.width
        if (self.ones >> bit) & 1:
            return '1'
        if (self.xs >> bit) & 1:
            return 'x'
        return '0'
