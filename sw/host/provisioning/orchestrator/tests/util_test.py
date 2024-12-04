# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import unittest

from util import resolve_runfile


class TestRunfileMustResolve(unittest.TestCase):

    def test_main_workspace_path(self):
        resolved = resolve_runfile(
            "sw/device/silicon_creator/manuf/keys/fake/dice_ca.pem")
        self.assertTrue(os.path.exists(resolved))

    def test_external_path(self):
        resolved = resolve_runfile(
            "external/openocd/tcl/interface/cmsis-dap.cfg")
        self.assertTrue(os.path.exists(resolved))

    def test_abs_path(self):
        path = os.path.abspath(__file__)
        resolved = resolve_runfile(path)
        self.assertEqual(path, resolved)

    def test_non_existent(self):
        with self.assertRaises(ValueError):
            resolve_runfile("file-does-not-exist")


if __name__ == '__main__':
    unittest.main()
