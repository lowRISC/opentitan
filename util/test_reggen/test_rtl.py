# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest

from reggen import gen_rtl


class TestFieldCheck(unittest.TestCase):
    def test_check_bool(self):
        arg = {'field1': "true", 'field2': "false", 'field3': "True"}
        result = gen_rtl.check_field_bool(arg, 'field1', False)
        self.assertTrue(result)
        result = gen_rtl.check_field_bool(arg, 'field2', True)
        self.assertFalse(result)
        result = gen_rtl.check_field_bool(arg, 'field3', False)
        self.assertFalse(result)
        result = gen_rtl.check_field_bool(arg, 'field4', False)
        self.assertFalse(result)
