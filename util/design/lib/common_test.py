#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from common import get_hd


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


if __name__ == '__main__':
    unittest.main()
