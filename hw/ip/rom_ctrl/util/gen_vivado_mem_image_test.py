#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest

from gen_vivado_mem_image import (UpdatememSimulator,
                                  otp_words_to_updatemem_pieces, swap_bytes)


class TestGenVivadoMemImage(unittest.TestCase):

    def test_swap_bytes(self) -> None:
        swapped = swap_bytes(39, 0x01, swap_nibbles=False)
        self.assertEqual(swapped, 0x0100000000)

        swapped = swap_bytes(39, 0x0102030405, swap_nibbles=False)
        self.assertEqual(swapped, 0x0504030201)

        swapped = swap_bytes(39, 0x0102030405, swap_nibbles=True)
        self.assertEqual(swapped, 0x5040302010)


class TestOtpWordsToUpdatememPieces(unittest.TestCase):

    def test_all_ones(self) -> None:
        words = [0x3fffff] * 4
        updatemem_pieces = otp_words_to_updatemem_pieces(words)
        expected = ["@0"] + \
            ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7
        self.assertEqual(updatemem_pieces, expected)

    def test_reverses_bits(self) -> None:
        words = [0x3df00d for _ in range(4)]
        updatemem_pieces = otp_words_to_updatemem_pieces(words)
        expected = ["@0"] + \
            ["B00FBC00000"] + ["00000000000"] * 7 + \
            ["B00FBC00000"] + ["00000000000"] * 7 + \
            ["B00FBC00000"] + ["00000000000"] * 7 + \
            ["B00FBC00000"] + ["00000000000"] * 7
        self.assertEqual(updatemem_pieces, expected)

    def test_many_words(self) -> None:
        words = [0x3df00d, 0x2df00d, 0x1df00d, 0x0df00d] * 4 + \
                [0x3fffff, 0x3fffff, 0x3fffff, 0x3fffff] * 3 + \
                [0x3df00d, 0x2df00d, 0x1df00d, 0x0df00d]
        updatemem_pieces = otp_words_to_updatemem_pieces(words)

        quadword1 = ["B00FBC00000"] + ["00000000000"] * 7 + \
            ["B00FB400000"] + ["00000000000"] * 7 + \
            ["B00FB800000"] + ["00000000000"] * 7 + \
            ["B00FB000000"] + ["00000000000"] * 7

        quadword2 = ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7 + \
            ["FFFFFC00000"] + ["00000000000"] * 7

        expected = ["@0"] + (quadword1 * 4) + (quadword2 * 3) + quadword1
        self.assertEqual(updatemem_pieces, expected)

    def test_updatemem_simulator(self) -> None:

        def make_init_line(num: int, data: int) -> str:
            return f"simulated INIT_{num:02X}: 256'h{data:064X}"

        all_zero_init_lines = [make_init_line(i, 0) for i in range(0x40)]

        updatemem = UpdatememSimulator(0x40, 22)
        updatemem.write_updatemem_hex_string('F')
        # The first four INIT_00 lines should end with '1'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            if i < 4:
                self.assertEqual(init_lines[0], make_init_line(0, 1))
                self.assertListEqual(init_lines[1:], all_zero_init_lines[1:])
            else:
                self.assertListEqual(init_lines, all_zero_init_lines)

        updatemem = UpdatememSimulator(0x40, 22)
        updatemem.write_updatemem_hex_string('FF')
        # The first eight INIT_00 lines should end with '1'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            if i < 8:
                self.assertEqual(init_lines[0], make_init_line(0, 1))
                self.assertListEqual(init_lines[1:], all_zero_init_lines[1:])
            else:
                self.assertListEqual(init_lines, all_zero_init_lines)

        updatemem = UpdatememSimulator(0x40, 22)
        updatemem.write_updatemem_hex_string('0F')
        # The first four INIT_00 lines should be zero, and the next four should
        # end with '1'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            if 4 <= i < 8:
                self.assertEqual(init_lines[0], make_init_line(0, 1))
                self.assertListEqual(init_lines[1:], all_zero_init_lines[1:])
            else:
                self.assertListEqual(init_lines, all_zero_init_lines)

        updatemem = UpdatememSimulator(0x40, 22)
        updatemem.write_updatemem_hex_string('FFFFFC')
        # All 22 INIT_00 lines should end with '1'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            self.assertEqual(init_lines[0], make_init_line(0, 1))
            self.assertListEqual(init_lines[1:], all_zero_init_lines[1:])

        updatemem = UpdatememSimulator(0x40, 22)
        updatemem.write_updatemem_hex_string('FFFFFFFFFFF')
        # All 22 INIT_00 lines should end with '3'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            self.assertEqual(init_lines[0], make_init_line(0, 0b11))
            self.assertListEqual(init_lines[1:], all_zero_init_lines[1:])

        updatemem = UpdatememSimulator(0x40, 22)
        for i in range(256):
            updatemem.write_updatemem_hex_string('FFFFFFFFFFF')
        # All INIT_00 and INIT_01 lines should be all 'F'.
        for i, init_lines in enumerate(updatemem.render_init_lines()):
            self.assertEqual(init_lines[0], make_init_line(0, 2**256 - 1))
            self.assertEqual(init_lines[1], make_init_line(1, 2**256 - 1))
            self.assertListEqual(init_lines[2:], all_zero_init_lines[2:])


if __name__ == '__main__':
    unittest.main()
