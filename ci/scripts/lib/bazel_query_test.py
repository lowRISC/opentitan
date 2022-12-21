# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import unittest
from unittest.mock import Mock

from bazel_query import BazelQuery, BazelQueryRunner


class TestBazelQuery(unittest.TestCase):

    def test_rule_exact(self):
        query = BazelQuery.rule_exact("foo", "bar")
        self.assertEqual(query, 'kind("^foo rule$", bar)')

    def test_tag_exact(self):
        query = BazelQuery.tag_exact("manual", "foo")
        self.assertEqual(query, 'attr("tags", "[\\[ ]manual[,\\]]", foo)')

    def test_regex_for_tag(self):
        regex = BazelQuery.regex_for_tag("foo")
        self.assertEqual(regex, '[\\[ ]foo[,\\]]')

        # Regex doesn't match lists without "foo".
        self.assertFalse(re.search(regex, "[]"))
        self.assertFalse(re.search(regex, "[bar]"))
        self.assertFalse(re.search(regex, "[bar, baz]"))

        # Regex does not match superstrings of "foo".
        self.assertFalse(re.search(regex, "[foobar]"))
        self.assertFalse(re.search(regex, "[barfoo]"))
        self.assertFalse(re.search(regex, "[foofoo]"))

        # Regex matches "foo" in any position.
        self.assertTrue(re.search(regex, "[bar, foo, baz]"))
        self.assertTrue(re.search(regex, "[bar, foo]"))
        self.assertTrue(re.search(regex, "[foo, baz]"))
        self.assertTrue(re.search(regex, "[foo]"))


class TestFindTargetsWithBannedChars(unittest.TestCase):

    def test_no_test_suites(self):
        backend = Mock()
        backend.return_value = []
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_targets_with_banned_chars()
        self.assertEqual(list(targets), [])

    def test_one_target_empty_string(self):
        """Bazel does not allow targets to have empty names.

        This test simply documents how we respond to the impossible scenario.
        """
        backend = Mock()
        backend.return_value = [""]
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_targets_with_banned_chars()
        self.assertEqual(list(targets), [])

    def test_only_good_chars(self):
        backend = Mock()
        backend.return_value = ["//foo:bar", "//bar_baz:foo"]
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_targets_with_banned_chars()
        self.assertEqual(list(targets), [])

    def test_only_bad_chars(self):
        backend = Mock()
        backend.return_value = ["!@#$", "^&*()", "\x01"]
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_targets_with_banned_chars()
        self.assertCountEqual(list(targets), [
            ("!@#$", set("!@#$")),
            ("^&*()", set("^&*()")),
            ("\x01", set("\x01")),
        ])

    def test_mixed(self):
        backend = Mock()
        backend.return_value = [
            '!@#$', '\x01', '//foo:bar', '^&*()', '//bar_baz:foo'
        ]
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_targets_with_banned_chars()
        self.assertCountEqual(list(targets), [
            ("!@#$", set("!@#$")),
            ("\x01", set("\x01")),
            ("^&*()", set("^&*()")),
        ])


class TestFindEmptyTestSuites(unittest.TestCase):

    def test_empty(self):
        backend = Mock()
        backend.return_value = []
        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_empty_test_suites()
        self.assertEqual(list(targets), [])

    def test_one_empty_suite(self):
        query_result_sequence = [
            ["//foo:some_test_suite"],  # List of test suites.
            [],  # List of tests in the first test suite.
        ]

        def backend(_query):
            return query_result_sequence.pop(0)

        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_empty_test_suites()
        self.assertEqual(list(targets), ["//foo:some_test_suite"])
        self.assertEqual(query_result_sequence, [])

    def test_second_suite_empty(self):
        query_result_sequence = [[
            "//foo:some_test_suite", "//foo:another_test_suite"
        ], ["//foo:test"], []]

        def backend(_query):
            return query_result_sequence.pop(0)

        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_empty_test_suites()
        self.assertEqual(list(targets), ["//foo:another_test_suite"])
        self.assertEqual(query_result_sequence, [])


class TestFindNonManualTestSuites(unittest.TestCase):

    def test_simple(self):
        backend = Mock()
        backend.return_value = ["//foo:bar"]

        bazel = BazelQueryRunner(backend=backend)
        targets = bazel.find_non_manual_test_suites()
        self.assertEqual(list(targets), ["//foo:bar"])
        backend.assert_called_once_with(
            'kind("^test_suite rule$", //...) except attr("tags", "[\\[ ]manual[,\\]]", //...)'
        )


if __name__ == '__main__':
    unittest.main()
