# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import string
import subprocess
from typing import Callable, Iterable, List, Set, Tuple


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

    def __init__(self, backend: Callable[[str], List[str]] = None):
        self._backend = backend

    def find_targets_with_banned_chars(self) -> Iterable[Tuple[str, Set[str]]]:
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
        allowed_chars = set(string.ascii_letters + string.digits + '/:_-.')
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

        Yields:
          Names of Bazel targets.
        """

        def print_progress(i, n):
            if n // 5 == 0 or i % (n // 5) == 0:
                print(self.find_empty_test_suites.__name__, end="")
                print(": Running query {}/{}...".format(i + 1, n))

        query_test_suites = BazelQuery.rule_exact("test_suite", "//...")
        all_test_suites = self.query(query_test_suites)

        for i, test_suite in enumerate(all_test_suites):
            print_progress(i, len(all_test_suites))
            tests = self.query("tests({})".format(test_suite))
            if len(tests) == 0:
                yield test_suite

    def find_non_manual_test_suites(self) -> Iterable[str]:
        """Find test_suite targets in //... that are not tagged with 'manual'."""
        query_pieces = [
            BazelQuery.rule_exact("test_suite", "//..."),
            "except",
            BazelQuery.tag_exact("manual", "//..."),
        ]
        query_str = " ".join(query_pieces)
        return self.query(query_str)

    def query(self, query: str) -> List[str]:
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
