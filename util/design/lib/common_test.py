#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
import re
import unittest
from common import blockify, get_hd, get_random_perm_hex_literal


class TestGetHd(unittest.TestCase):

    def test_different_length_words(self):
        with self.assertRaises(RuntimeError):
            get_hd('010101', '0101010101')

    def test_0b_prefixed_words(self):
        with self.assertRaises(ValueError):
            get_hd('10101', '0b101')

    def test_all_zeros(self):
        self.assertEqual(get_hd('0000', '0000'), 0)

    def test_all_ones(self):
        self.assertEqual(get_hd('1111', '1111'), 0)

    def test_nonzero_hd(self):
        self.assertEqual(get_hd('100101', '010100'), 3)


def _parse_blockify_output(literal):
    '''Reconstruct the integer and total bit width encoded by a blockify() literal.'''
    total_bits = 0
    hex_digits = ""
    for width_str, digits in re.findall(r"(\d+)'h([0-9a-fA-F_]+)", literal):
        total_bits += int(width_str)
        hex_digits += digits.replace('_', '')
    return int(hex_digits, 16), total_bits


class TestBlockify(unittest.TestCase):

    def test_round_trip_nibble_aligned(self):
        # Sizes that are a multiple of 4 should round-trip correctly.
        for size in (32, 64, 256, 2048):
            val = random.getrandbits(size)
            got_val, got_bits = _parse_blockify_output(blockify(hex(val), size, 64))
            self.assertEqual(got_bits, size)
            self.assertEqual(got_val, val)

    def test_round_trip_non_nibble_aligned(self):
        # Sizes that are not divisible by 4 should round-trip correctly.
        for size in (173, 389 * 9, 1, 2, 3, 4001):
            val = random.getrandbits(size)
            got_val, got_bits = _parse_blockify_output(blockify(hex(val), size, 64))
            self.assertEqual(got_bits, size)
            self.assertEqual(got_val, val)

    def test_round_trip_leading_zero_value(self):
        # If the random value happens to have leading zero bits, hex()/int() drop them.
        # Check that that doesn't lead to any misalignment.
        val = 0x1f
        size = 173
        got_val, got_bits = _parse_blockify_output(blockify(hex(val), size, 64))
        self.assertEqual(got_bits, size)
        self.assertEqual(got_val, val)

    def test_fuzz_round_trip(self):
        for _ in range(200):
            size = random.randint(1, 4000)
            val = random.getrandbits(size)
            got_val, got_bits = _parse_blockify_output(blockify(hex(val), size, 64))
            self.assertEqual(got_bits, size)
            self.assertEqual(got_val, val)


class TestGetRandomPermHexLiteral(unittest.TestCase):

    def _check_is_permutation(self, num_elements):
        literal = get_random_perm_hex_literal(num_elements)
        val, total_bits = _parse_blockify_output(literal)
        width = (num_elements - 1).bit_length()
        self.assertEqual(total_bits, num_elements * width)
        mask = (1 << width) - 1
        indices = [(val >> (i * width)) & mask for i in range(num_elements)]
        self.assertEqual(sorted(indices), list(range(num_elements)))

    def test_nibble_aligned_width(self):
        # Nibble-aligned test.
        self._check_is_permutation(256)

    def test_non_nibble_aligned_width(self):
        # Non nibble-aligned test.
        self._check_is_permutation(389)

    def test_boundary_sizes(self):
        # Corner cases around the log ceil of different sizes.
        for num_elements in (2, 5, 17, 100, 255, 256, 257, 500, 1000):
            self._check_is_permutation(num_elements)

    def test_fuzz_random_sizes(self):
        for _ in range(100):
            num_elements = random.randint(2, 4000)
            self._check_is_permutation(num_elements)


if __name__ == '__main__':
    unittest.main()
