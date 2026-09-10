# Copyright lowRISC contributors (OpenTitan project).
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


def suite_rule(name, tests=None, implicit_tests=None, tags=None):
    """Build the rule dict Bazel emits for a test_suite target.

    Bazel omits `stringListValue` for an attribute with no values, which is how
    an empty and an unset list look alike in its output.
    """

    def attr(attr_name, values):
        entry = {"name": attr_name, "type": "STRING_LIST"}
        if values:
            entry["stringListValue"] = list(values)
        return entry

    return {
        "name": name,
        "ruleClass": "test_suite",
        "attribute": [
            attr("tests", tests),
            attr("$implicit_tests", implicit_tests),
            attr("tags", tags),
        ],
    }


class FakeBazel:
    """A stand-in for Bazel that answers from a declared set of suites.

    `expansions` overrides what `tests(<suite>)` reports for a given suite,
    which is how the tests distinguish the declared graph from the answer Bazel
    would give for it.
    """

    def __init__(self, suites, tests=(), expansions=None):
        self.suites = suites
        self.tests = list(tests)
        self.expansions = expansions or {}
        self.queries = []

    def labels(self, query):
        self.queries.append(query)
        if query == "tests(//...)":
            return self.tests
        if query.startswith("tests(") and query.endswith(")"):
            return list(self.expansions.get(query[len("tests("):-1], []))
        raise AssertionError("unexpected query: " + query)

    def rules(self, query):
        self.queries.append(query)
        assert query == 'kind("^test_suite rule$", //...)', query
        return self.suites

    def runner(self):
        return BazelQueryRunner(backend=self.labels, rule_backend=self.rules)


class TestFindEmptyTestSuites(unittest.TestCase):

    def test_no_suites(self):
        bazel = FakeBazel(suites=[])
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])

    def test_suite_with_a_test(self):
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite", tests=["//foo:test"])],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])

    def test_suite_with_no_members(self):
        bazel = FakeBazel(suites=[suite_rule("//foo:suite")])
        self.assertEqual(list(bazel.runner().find_empty_test_suites()),
                         ["//foo:suite"])

    def test_suite_of_nonexistent_labels(self):
        """A member that names nothing at all does not count as a test."""
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite", tests=["//foo:typo"])],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()),
                         ["//foo:suite"])

    def test_implicit_tests_used_when_tests_omitted(self):
        """An omitted `tests` attribute selects the package's own tests."""
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite", implicit_tests=["//foo:test"])],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])

    def test_nested_suite_holding_a_test(self):
        bazel = FakeBazel(
            suites=[
                suite_rule("//foo:outer", tests=["//foo:inner"]),
                suite_rule("//foo:inner", tests=["//foo:test"]),
            ],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])

    def test_nested_empty_suite(self):
        """Emptiness propagates up through nested suites."""
        bazel = FakeBazel(suites=[
            suite_rule("//foo:outer", tests=["//foo:inner"]),
            suite_rule("//foo:inner"),
        ])
        self.assertCountEqual(list(bazel.runner().find_empty_test_suites()),
                              ["//foo:outer", "//foo:inner"])

    def test_cycle_between_suites(self):
        """A cycle terminates. Bazel rejects these, so any answer will do."""
        bazel = FakeBazel(suites=[
            suite_rule("//foo:a", tests=["//foo:b"]),
            suite_rule("//foo:b", tests=["//foo:a"]),
        ])
        self.assertCountEqual(list(bazel.runner().find_empty_test_suites()),
                              ["//foo:a", "//foo:b"])

    def test_candidate_that_bazel_says_is_not_empty(self):
        """The confirming `tests()` query overrules the resolution here."""
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite", tests=["//foo:surprise"])],
            expansions={"//foo:suite": ["//foo:surprise"]},
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])

    def test_tagged_suite_is_confirmed_by_query(self):
        """Tags filter a suite's contents, so its members settle nothing.

        The suite lists a test, but its tags may exclude it. It is checked
        against Bazel either way, and here Bazel reports it empty.
        """
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite",
                               tests=["//foo:test"],
                               tags=["verilator"])],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()),
                         ["//foo:suite"])
        self.assertIn("tests(//foo:suite)", bazel.queries)

    def test_manual_tag_does_not_filter_contents(self):
        """`manual` keeps a suite out of wildcards; it drops no tests."""
        bazel = FakeBazel(
            suites=[suite_rule("//foo:suite",
                               tests=["//foo:test"],
                               tags=["manual"])],
            tests=["//foo:test"],
        )
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])
        self.assertNotIn("tests(//foo:suite)", bazel.queries)

    def test_no_query_per_suite(self):
        """Suites are resolved in bulk; only candidates are queried."""
        suites = [
            suite_rule(f"//foo:suite{i}", tests=["//foo:test"])
            for i in range(100)
        ]
        bazel = FakeBazel(suites=suites, tests=["//foo:test"])
        self.assertEqual(list(bazel.runner().find_empty_test_suites()), [])
        self.assertEqual(bazel.queries, [
            'kind("^test_suite rule$", //...)',
            "tests(//...)",
        ])


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
