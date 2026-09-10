# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import json
import string
import subprocess
from collections.abc import Callable, Iterable
from typing import NamedTuple

# Tags on a test_suite that Bazel does not use to filter the suite's contents.
# Every other tag acts as a filter on the tests in the suite, so a suite
# carrying one cannot be resolved from the build graph alone.
NON_FILTERING_SUITE_TAGS = frozenset(["manual"])


class TestSuite(NamedTuple):
    """The contents of a test_suite target, as declared in the BUILD file."""

    # Labels of the suite's members. These are the labels of the `tests`
    # attribute, or, when that attribute is omitted, the tests Bazel implicitly
    # picked up from the suite's own package. A label here need not name a test:
    # it may name a nested test_suite, a non-test rule, or nothing at all.
    members: list[str]
    tags: list[str]

    def filters_contents(self) -> bool:
        """Whether this suite's tags drop members from its expansion."""
        return bool(set(self.tags) - NON_FILTERING_SUITE_TAGS)


class BazelQuery:
    """A collection of functions useful for constructing Bazel queries."""

    @staticmethod
    def rule_exact(rule: str, input: str) -> str:
        """Match targets in `input` defined by `rule`."""
        return f'kind("^{rule} rule$", {input})'

    @staticmethod
    def tag_exact(tag: str, input: str) -> str:
        """Match targets in `input` that are tagged with `tag`."""
        regex = BazelQuery.regex_for_tag(tag)
        return f'attr("tags", "{regex}", {input})'

    @staticmethod
    def regex_for_tag(tag: str) -> str:
        """Build a regex to find the given tag in a list.

        The query `attr("tags", pattern, input)` would match the given pattern
        against a serialized list of tags, e.g. `[foo, bar]`. Subtly, if the
        pattern is "foo", it will also match targets that are tagged "foobar".

        This function constructs a regex that matches only when the list of tags
        actually contains `tag`, not just a superstring of `tag`, as recommended
        by the Bazel query docs: https://bazel.build/query/language#attr
        """
        return f"[\\[ ]{tag}[,\\]]"


class BazelQueryRunner:

    def __init__(self,
                 backend: Callable[[str], list[str]] | None = None,
                 rule_backend: Callable[[str], list[dict]] | None = None):
        self._backend = backend
        self._rule_backend = rule_backend

    def find_targets_with_banned_chars(self) -> Iterable[tuple[str, set[str]]]:
        """Find targets in //... with names containing disallowed characters.

        Bazel allows a liberal set of characters in target names [0], which
        enables type confusion bugs to go unnoticed. For example, a tuple's
        string representation, complete with parentheses and commas, can
        accidentally be inserted into a target name via `string.format()`.

        [0]: https://bazel.build/concepts/labels#target-names

        Yields:
          A tuple for each target that has banned characters in its name. The
          first element is the Bazel target's name. The second element is the
          set of characters that must be removed from the target's name.

        """
        allowed_chars = set(string.ascii_letters + string.digits + '/:_-.+')
        for target in self.query("//..."):
            if bad_chars := set(target) - allowed_chars:
                yield (target, bad_chars)

    def find_empty_test_suites(self) -> Iterable[str]:
        """Find test_suite targets in //... that contain zero tests.

        Finding empty test suites is not as simple as querying for test_suite
        targets where `tests = []`. In fact, that is a special case of
        test_suite that causes it to select all tests in the package.

        There are a few ways to wind up with an empty test suite. One way is to
        provide a nonempty `tests` argument containing only nonexistent labels.
        Another way is to provide a non-empty list of tests that exist, but to
        specify `tags` that exclude all the tests.

        `tests(suite)` answers the question directly, but running it per suite
        meant ~1600 Bazel invocations, over four minutes, and the slowest check
        in the lint stage. Instead, the declared contents of every suite are
        read in one query and resolved here: a suite holds a test if any of its
        members is a test target, or is a suite that itself holds one. That
        settles all but a handful of suites, and each remaining candidate is
        then confirmed with the `tests(suite)` query it would have run anyway,
        so what this reports does not rest on the resolution being faithful.

        Yields:
          Names of Bazel targets.
        """
        suites = self.test_suite_contents()
        tests = set(self.query("tests(//...)"))
        holds_test = self._suites_holding_tests(suites, tests)
        for suite in suites:
            if suite not in holds_test and not self.query(f"tests({suite})"):
                yield suite

    @staticmethod
    def _suites_holding_tests(suites: dict[str, TestSuite],
                              tests: set[str]) -> set[str]:
        """Of `suites`, those that resolve to at least one test target.

        A member label that names neither a test nor a suite counts for
        nothing, which is how nonexistent members and non-test rules drop out.

        A suite whose tags filter its contents is left out even when it lists
        members, because how many of them survive the filter is not visible
        here. That is the safe direction: it makes the suite a candidate, and
        the confirming `tests()` query has the final say.
        """
        resolved: dict[str, bool] = {}

        def holds_test(label: str) -> bool:
            if label in tests:
                return True
            suite = suites.get(label)
            if suite is None or suite.filters_contents():
                return False
            if label not in resolved:
                # Seed as False so a cycle among suites terminates. Bazel
                # rejects dependency cycles, so this only guards against
                # pathological input.
                resolved[label] = False
                resolved[label] = any(holds_test(m) for m in suite.members)
            return resolved[label]

        return {suite for suite in suites if holds_test(suite)}

    @staticmethod
    def _string_list_attr(rule: dict, name: str) -> list[str]:
        """Read a string-list attribute of a rule.

        Bazel omits the value entirely for an attribute with no entries, so an
        empty list and an unset one look the same here.
        """
        for attr in rule.get("attribute", []):
            if attr["name"] == name:
                return list(attr.get("stringListValue", []))
        return []

    def test_suite_contents(self) -> dict[str, TestSuite]:
        """Read the declared contents of every test_suite in //...."""
        contents = {}
        query = BazelQuery.rule_exact("test_suite", "//...")
        for rule in self.query_rules(query):
            # An omitted `tests` attribute makes Bazel populate the implicit
            # one with every test in the suite's package.
            members = (self._string_list_attr(rule, "tests")
                       or self._string_list_attr(rule, "$implicit_tests"))
            contents[rule["name"]] = TestSuite(
                members=members, tags=self._string_list_attr(rule, "tags"))
        return contents

    def find_non_manual_test_suites(self) -> Iterable[str]:
        """Find test_suite targets in //... that are not tagged with 'manual'."""
        query_pieces = [
            BazelQuery.rule_exact("test_suite", "//..."),
            "except",
            BazelQuery.tag_exact("manual", "//..."),
        ]
        query_str = " ".join(query_pieces)
        return self.query(query_str)

    def query(self, query: str) -> list[str]:
        """Perform a Bazel query and return the resulting targets."""
        if self._backend:
            return self._backend(query)

        bazel = subprocess.run(
            ["./bazelisk.sh", "query", "--output=label", query],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            encoding='utf-8',
            check=True)
        stdout_lines = bazel.stdout.split('\n')
        return [s for s in stdout_lines if s != ""]

    def query_rules(self, query: str) -> list[dict]:
        """Perform a Bazel query, returning the matched rules and attributes.

        Unlike `query`, which yields bare labels, this asks Bazel for each
        target's rule definition. Only rules are returned; source files and
        package groups in the result are dropped.
        """
        if self._rule_backend:
            return self._rule_backend(query)

        bazel = subprocess.run(
            ["./bazelisk.sh", "query", "--output=streamed_jsonproto", query],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            encoding='utf-8',
            check=True)
        targets = [json.loads(line) for line in bazel.stdout.splitlines() if line]
        return [t["rule"] for t in targets if t.get("type") == "RULE"]
