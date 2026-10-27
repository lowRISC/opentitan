#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for OpenTitan's PRINCE64 cipher implementation."""

import unittest

from prince import PRINCE_SBOX4, PRINCE_SBOX4_INV, prince, sbox

# PRINCE test vectors (plaintext, key, half-rounds, ciphertext).
# OpenTitan uses the original PRINCE (i.e. not PRINCEv2), with a modified
# key schedule as proposed by Dinur in "Cryptanalytic Time-Memory-Data Tradeoffs
# for FX-Constructions with Applications to PRINCE and PRIDE" (EUROCRYPT 2015).
# We hence include some basic KATs from the original PRINCE paper, and custom KATs.
KAT_VECTORS = [
    # All 0s and all 1s, for a standard 5 half-rounds.
    (0x0000000000000000, 0x00000000000000000000000000000000, 5, 0x818665aa0d02dfda),
    (0xffffffffffffffff, 0x00000000000000000000000000000000, 5, 0x604ae6ca03c20ada),
    # Custom: tests variable half-rounds, and OT's key schedule
    (0x0123456789abcdef, 0x00112233445566778899aabbccddeeff, 5, 0x05437c97cd7cf13a),
    (0x0123456789abcdef, 0x00112233445566778899aabbccddeeff, 2, 0xe065420998fec3f1),
    (0xdeadbeefcafef00d, 0x13579bdf2468ace00f1e2d3c4b5a6978, 1, 0xfacfbf4d91b493b5),
    (0x5a5a5a5aa5a5a5a5, 0xa5a5a5a55a5a5a5a3c3c3c3cc3c3c3c3, 3, 0xca25b8b2dca22f3d),
    # Only one of k0 and k1 set.
    (0x0000000000000000, 0xffffffffffffffff0000000000000000, 5, 0x85fbb8384134642f),
    (0x0000000000000000, 0x0000000000000000ffffffffffffffff, 5, 0xb1d7cd0a0bf97915),
]


class TestPrince(unittest.TestCase):
    """Unit tests for OpenTitan's PRINCE64 cipher block."""

    def test_kat(self) -> None:
        """Test a mixture of Known Answer Test vectors."""
        for data, key, rounds, expected in KAT_VECTORS:
            self.assertEqual(prince(data, key, rounds), expected,
                             msg=f"data={data:#x} key={key:#x}, rounds={rounds}")

    def test_invalid_arguments(self) -> None:
        """Test that the PRINCE cipher interface rejects invalid arguments."""
        # Invalid data word
        with self.assertRaises(AssertionError):
            prince(-1, 0, 5)
        with self.assertRaises(AssertionError):
            prince(1 << 64, 0, 5)
        # Invalid key
        with self.assertRaises(AssertionError):
            prince(0, -1, 5)
        with self.assertRaises(AssertionError):
            prince(0, 1 << 128, 5)
        # Invalid number of rounds
        with self.assertRaises(AssertionError):
            prince(0, 0, -1)
        with self.assertRaises(AssertionError):
            prince(0, 0, 6)

    def test_sbox_inverse(self) -> None:
        """Test that the PRINCE S-box inverse correctly reverts the S-box."""
        for value in range(16):
            self.assertEqual(sbox(sbox(value, 4, PRINCE_SBOX4), 4, PRINCE_SBOX4_INV), value,
                             msg=f"value={value:#x}")


if __name__ == '__main__':
    unittest.main()
