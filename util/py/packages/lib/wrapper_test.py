#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest

from util.py.packages.lib.wrapper import Wrapper


class TestWrapper(unittest.TestCase):

    def test_not_initialized(self):
        w = Wrapper()
        with self.assertRaisesRegex(RuntimeError, "not initialized"):
            w.foo

    def test_replace_wrapped(self):
        w = Wrapper()
        w.replace_wrapped(5)
        self.assertEqual(w.to_bytes(1, "little"), b'\x05')
        w.replace_wrapped(7)
        self.assertEqual(w.to_bytes(1, "little"), b'\x07')


if __name__ == "__main__":
    unittest.main()
