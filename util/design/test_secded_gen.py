#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for SECDED ECC encoding functions."""

import random
import unittest

import secded_gen

_CONFIGS = secded_gen.load_secded_configs()
_TEST_RND_SEED = 123


def _get_test_words(k: int, rnd: random.Random, count: int) -> list[int]:
    """Gets some test words of size `k`, which includes some predefined edge cases
    used for each parameterized test, and `count` random words."""
    default_cases = [
        0,
        1,
        (1 << k) - 1,  # All 1s
        1 << (k - 1),  # MSB only set
        int("01" * k, 2) & ((1 << k) - 1)  # Alternating 01 bit-pattern
    ]
    return default_cases + [rnd.getrandbits(k) for _ in range(count)]


class TestSecdedEccEncode(unittest.TestCase):
    """Unit tests for SECDED ECC encoding functions."""

    def test_kat(self) -> None:
        """Test with some Known Answer Test vectors, taken from the RTL encoders."""
        vectors = [
            ("hamming", 64, 0x0123456789abcdef, 0x9c0123456789abcdef),
            ("hamming", 64, 0xffffffffffffffff, 0xffffffffffffffffff),
            ("hamming", 68, 0xf0123456789abcdef, 0x9cf0123456789abcdef),
            ("inv_hsiao", 32, 0x89abcdef, 0x3e89abcdef),
            ("inv_hsiao", 32, 0xffffffff, 0x2affffffff),
        ]
        for codetype, k, word, expected in vectors:
            encoded = secded_gen.ecc_encode(codetype, k, word)[0]
            self.assertEqual(encoded, expected, msg=f"{codetype} k={k} word={word:#x}")

    def test_encoded_layout(self) -> None:
        """Test that the check bits prefix the data bits, which are unchanged."""
        rnd = random.Random(_TEST_RND_SEED)
        for cfg in _CONFIGS:
            codetype = cfg["code_type"]
            k = cfg["k"]
            m = cfg["m"]
            for word in _get_test_words(k, rnd, 20):
                error_context = f"{codetype} k={k} word={word:#x}"
                codeword, check_bits = secded_gen.ecc_encode(codetype, k, word)
                self.assertEqual(check_bits, m, msg=error_context)
                self.assertEqual(codeword & ((1 << k) - 1), word, msg=error_context)
                self.assertLess(codeword, 1 << (k + m), msg=error_context)

    def test_detects_single_and_double_bit_errors(self) -> None:
        """Test SECDED detection: single or double errors should not produce the same encoding."""
        rnd = random.Random(_TEST_RND_SEED + 1)
        for cfg in _CONFIGS:
            codetype = cfg["code_type"]
            k = cfg["k"]
            m = cfg["m"]
            num_bits = k + m
            data_mask = (1 << k) - 1
            for word in _get_test_words(k, rnd, 2):
                codeword = secded_gen.ecc_encode(codetype, k, word)[0]
                for num_flips in (1, 2):
                    for _ in range(25):
                        flips = rnd.sample((range(num_bits)), num_flips)
                        corrupted = codeword
                        for index in flips:
                            corrupted ^= (1 << index)
                        re_encoded = secded_gen.ecc_encode(codetype, k, corrupted & data_mask)[0]
                        self.assertNotEqual(corrupted, re_encoded,
                                            msg=f"{codetype} k={k} word={word:#x} flips={flips}")

    def test_unsupported_code(self) -> None:
        """Test that unsupported code types or key sizes appropriately error."""
        with self.assertRaises(Exception):
            secded_gen.ecc_encode("hamming", 17, 0)
        with self.assertRaises(Exception):
            secded_gen.ecc_encode("hamming", 15, 0)
        with self.assertRaises(Exception):
            secded_gen.ecc_encode("invalid", 64, 0)
        with self.assertRaises(Exception):
            secded_gen.ecc_encode("_hamming", 16, 0)

    def test_invalid_input_word(self) -> None:
        """Test that invalid data words appropriately error."""
        with self.assertRaises(AssertionError):
            secded_gen.ecc_encode("hamming", 64, 1 << 64)
        with self.assertRaises(AssertionError):
            secded_gen.ecc_encode("hamming", 64, -1)


if __name__ == "__main__":
    unittest.main()
