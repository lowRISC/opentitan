#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
import unittest.mock

import io
import contextlib
import re

from lib.common import get_hd
import importlib

enc = importlib.import_module("sparse-fsm-encode")


class TestCheckCandidate(unittest.TestCase):

    def setUp(self):
        self.generator = enc.EncodingGenerator(min_hd=3,
                                               num_states=8,
                                               encoding_len=8,
                                               seed=1234567890,
                                               language="c",
                                               avoid_zero=True)
        self.generator.encodings = ['00111010']

    def test_reject_existing_candidate(self):
        self.assertFalse(self.generator._check_candidate('00111010'))

    def test_valid_candidate(self):
        candidate = '01001010'
        self.assertEqual(get_hd(candidate, self.generator.encodings[0]), 3)
        self.assertTrue(self.generator._check_candidate(candidate))

    def test_low_hamming_dist(self):
        candidate = '10011010'
        self.assertEqual(get_hd(candidate, self.generator.encodings[0]), 2)
        self.assertFalse(self.generator._check_candidate(candidate))

    def test_inverse_candidate(self):
        self.assertFalse(self.generator._check_candidate('11000101'))

    def test_all_ones(self):
        self.assertFalse(self.generator._check_candidate('11111111'))

    def test_all_zeros(self):
        self.assertFalse(self.generator._check_candidate('00000000'))

    def test_avoid_zero(self):
        self.assertFalse(self.generator._check_candidate('10000100'))

    def test_no_avoid_zero(self):
        noAvoidZeroGenerator = enc.EncodingGenerator(min_hd=3,
                                                     num_states=8,
                                                     encoding_len=8,
                                                     seed=1234567890,
                                                     language="c",
                                                     avoid_zero=False)
        self.assertTrue(noAvoidZeroGenerator._check_candidate('00000100'))


class TestArgsParsing(unittest.TestCase):

    def test_disallowed_encoding_lengths(self):
        # Only 8, 16, and 32-bit encodings can be generated for C and Rust
        # languages.
        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '8', '-m', '30', '-n', '30',
                '-s', '1234567890', '--language', 'c'
        ]):
            with self.assertRaises(SystemExit) as e, self.assertLogs(
                    'root', level='ERROR') as logs:
                enc.main()
            self.assertEqual(e.exception.code, 1)
            self.assertTrue(
                any('When using C or Rust, widths must be a power-of-two' in
                    log for log in logs.output))

        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '8', '-m', '30', '-n', '30',
                '-s', '1234567890', '--language', 'rust'
        ]):
            with self.assertRaises(SystemExit) as e, self.assertLogs(
                    'root', level='ERROR') as logs:
                enc.main()
            self.assertEqual(e.exception.code, 1)
            self.assertTrue(
                any('When using C or Rust, widths must be a power-of-two' in
                    log for log in logs.output))

    def test_too_few_states(self):
        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '8', '-m', '1', '-n', '32', '-s',
                '1234567890', '--language', 'rust'
        ]):
            with self.assertRaises(SystemExit) as e, self.assertLogs(
                    'root', level='ERROR') as logs:
                enc.main()
            self.assertEqual(e.exception.code, 1)
            self.assertTrue(
                any('Number of states (m) must be at least 2' in log
                    for log in logs.output))

    def test_too_many_states(self):
        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '4', '-m', '1024', '-n', '8',
                '-s', '1234567890', '--language', 'rust'
        ]):
            with self.assertRaises(SystemExit) as e, self.assertLogs(
                    'root', level='ERROR') as logs:
                enc.main()
            self.assertEqual(e.exception.code, 1)
            r = r'.*Statespace 2\^[0-9]+ not large enough to accommodate [0-9]+ states.*'
            self.assertTrue(any(re.match(r, log) for log in logs.output))

    def test_encoding_too_small(self):
        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '8', '-m', '10', '-n', '8', '-s',
                '1234567890', '--language', 'sv'
        ]):
            with self.assertRaises(SystemExit) as e, self.assertLogs(
                    'root', level='ERROR') as logs:
                enc.main()
            self.assertEqual(e.exception.code, 1)
            r = (r'.*State is only [0-9]+ bits wide, which is not enough to '
                 r'fulfill a minimum Hamming distance constraint of [0-9]\.')
            self.assertTrue(any(re.match(r, log) for log in logs.output))

    def test_too_small_hamming_dist(self):
        with unittest.mock.patch('sys.argv', [
                'sparse-fsm-encode.py', '-d', '2', '-m', '12', '-n', '32',
                '-s', '1234567890', '--language', 'sv'
        ]):
            with self.assertLogs('root', level='WARN') as logs:
                enc.main()
            warning_string = (
                'A value of 4-5 is recommended for the minimum Hamming '
                'distance constraint. At a minimum, this should be set to 3.')
            self.assertTrue(any(warning_string in log for log in logs.output))


class TestIdempotency(unittest.TestCase):

    def test_idempotency(self):
        """Call the script 10 times and check that the output doesn't change."""
        outputs = list()
        for i in range(10):
            f = io.StringIO()
            with contextlib.redirect_stdout(f):
                with unittest.mock.patch('sys.argv', [
                        'sparse-fsm-encode.py', '-d', '8', '-m', '30', '-n',
                        '32', '-s', '1234567890', '--language', 'sv'
                ]):
                    enc.main()
            outputs.append(f.getvalue())
        self.assertTrue(len(set(outputs)) == 1)


class TestBackwardsCompatibility(unittest.TestCase):

    def test_backwards_compatibility(self):
        """Ensure that a known seed generates the expected encodings."""
        generator = enc.EncodingGenerator(min_hd=6,
                                          num_states=10,
                                          encoding_len=32,
                                          seed=3775359077,
                                          language="c",
                                          avoid_zero=True)
        generator.generate()
        self.assertEqual(generator.encodings, [
            '11101110000100110101010110000000',
            '01100100010000110011010000111111',
            '10100111000000100111001101000101',
            '00110010100011110010111100111110',
            '01110000111111001011001001111111',
            '00111010110011111010000111000111',
            '01111101000110010011000110010100',
            '11100000101111000001010011100000',
            '10010001001000000111011110000101',
            '11010100110010100111001010100010'
        ])


if __name__ == "__main__":
    unittest.main(buffer=True)  # hide the printed output with buffer = True
