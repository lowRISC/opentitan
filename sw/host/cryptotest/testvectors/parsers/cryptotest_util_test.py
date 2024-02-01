# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import tempfile
import os
import unittest

from cryptotest_util import parse_rsp


def createRsp(content: bytes) -> str:
    with tempfile.NamedTemporaryFile(delete=False, dir=os.environ["TEST_TMPDIR"]) as temp:
        temp.write(content)
        return temp.name


class RspTests(unittest.TestCase):

    """Check that we can parse headers and variables."""
    def test_simple(self):
        rsp = createRsp(b"""
[section name]

x = 1234
y = 5678

""")
        expected = [{
            "section_name": "section name",
            "x": "1234",
            "y": "5678",
        }]
        self.assertEqual(expected, parse_rsp(rsp, []))

    def test_no_trailing_newline(self):
        """Check that we can parse a test case at the end of the file with no trailing newline."""
        rsp = createRsp(b"""
[section name]

x = 1234
y = 5678
""")
        expected = [{
            "section_name": "section name",
            "x": "1234",
            "y": "5678",
        }]
        self.assertEqual(expected, parse_rsp(rsp, []))

    def test_csv_header(self):
        """Check that we can operate without headers and parse multiple test cases."""
        rsp = createRsp(b"""
[a, b, c]
x = 1234
y = 5678

""")
        expected = [
            {
                "section_name": ["a", "b", "c"],
                "x": "1234",
                "y": "5678",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, ["m", "n"]))

    def test_multiple_tests_no_headers(self):
        """Check that we can operate without headers and parse multiple test cases."""
        rsp = createRsp(b"""
x = 1234
y = 5678

x = 1111
y = 2222
""")
        expected = [
            {
                "x": "1234",
                "y": "5678",
            },
            {
                "x": "1111",
                "y": "2222",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, ["m", "n"]))

    def test_header_variables(self):
        """Check that header variables are stored persistently."""
        rsp = createRsp(b"""
[section name]
[a = hello]
[b = world]

x = 1234
y = 5678

x = 1111
y = 2222
""")
        expected = [
            {
                "section_name": "section name",
                "a": "hello",
                "b": "world",
                "x": "1234",
                "y": "5678",
            },
            {
                "section_name": "section name",
                "a": "hello",
                "b": "world",
                "x": "1111",
                "y": "2222",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, []))

    def test_header_delimiter(self):
        """Check that headers can delimit test cases."""
        rsp = createRsp(b"""
[a = hello]
x = 1234
y = 5678
[a = world]
x = 1111
y = 2222
""")
        expected = [
            {
                "a": "hello",
                "x": "1234",
                "y": "5678",
            },
            {
                "a": "world",
                "x": "1111",
                "y": "2222",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, []))

    def test_persistent_variables(self):
        """Check that the user-specified persistent variables are respected."""
        rsp = createRsp(b"""
m = 1
n = 2
o = 3

x = 1234
y = 5678

x = 1111
y = 2222
""")
        expected = [
            {
                "m": "1",
                "n": "2",
                "x": "1234",
                "y": "5678",
            },
            {
                "m": "1",
                "n": "2",
                "x": "1111",
                "y": "2222",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, ["m", "n"]))

    def test_duplicate_variables(self):
        """Check that duplicate values of variables in the same group are stored in lists."""
        rsp = createRsp(b"""
m = abc
m = def

n = efg

n = hij

x = 1234
y = 5678
x = 1111
y = 2222

x = 3333
y = 4444
""")
        expected = [
            {
                "m": ["abc", "def"],
                # Should not duplicate, because the copies are in different groups
                "n": "hij",
                "x": ["1234", "1111"],
                "y": ["5678", "2222"],
            },
            {
                "m": ["abc", "def"],
                "n": "hij",
                "x": "3333",
                "y": "4444",
            },
        ]
        self.assertEqual(expected, parse_rsp(rsp, ["m", "n"]))


if __name__ == '__main__':
    unittest.main()
