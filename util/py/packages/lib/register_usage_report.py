# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import collections
import dataclasses
import functools
import pickle
from typing import Optional

import clang.cindex

from util.py.packages.lib import ot_logging

log = ot_logging.log


@dataclasses.dataclass
class SingleFileSourceRange:
    """Represents a range of lines in a source file.

    It's like clang.cindex.SourceRange, but hashable and serializable.
    Critically, we can be certain it does not contain any pointers to libclang
    objects.
    """
    path: str
    line_begin: int
    line_end: int

    @staticmethod
    def from_source_range(
            extent: clang.cindex.SourceRange) -> 'SingleFileSourceRange':
        start: clang.cindex.SourceLocation = extent.start
        end: clang.cindex.SourceLocation = extent.end

        if start.file.name != end.file.name:
            # It should be impossible for libclang to return an extent that
            # spans files.
            raise Exception(
                "SingleFileSourceRange cannot span files: {}, {}".format(
                    start.file.name, end.file.name))
        return SingleFileSourceRange(start.file.name, start.line, end.line)

    def __hash__(self):
        return hash((self.path, self.line_begin, self.line_end))

    def preview(self) -> str:
        """Construct a multi-line string showing context around this source range."""
        NUM_CONTEXT_LINES = 2

        with open(self.path) as f:
            lines = f.readlines()
        line_begin = max(0, self.line_begin - NUM_CONTEXT_LINES)
        lines = lines[line_begin:self.line_end + NUM_CONTEXT_LINES + 1]
        preview_lines = [
            f"{self.path}:{line_begin + i + 1}  {s.rstrip()}"
            for i, s in enumerate(lines)
        ]
        return "\n".join(preview_lines)


@dataclasses.dataclass
class RegisterUsageReport:
    """A report that says which registers are passed to the named function.

    Fields:
      function_name: The function this report is about.
      registers_to_callsites: Maps register tokens to callsites.
      unparsed_callsites: Callsites where a register could not be automatically
        detected. These are included because they require human review.
    """
    function_name: str
    registers_to_callsites: dict[str, set[SingleFileSourceRange]]
    unparsed_callsites: set[SingleFileSourceRange]

    @staticmethod
    def merge_reports(
        reports: list['RegisterUsageReport']
    ) -> Optional['RegisterUsageReport']:
        if len(reports) == 0:
            return None

        functions = set(r.function_name for r in reports)
        if len(functions) != 1:
            raise Exception(
                f"Reports unexpectly cover {len(functions)} functions: " +
                f"{sorted(list(functions))}")
        function_name = functions.pop()

        registers_to_callsites: dict[
            str, set[SingleFileSourceRange]] = collections.defaultdict(set)
        unparsed_callsites = set()

        for report in reports:
            for register, callsites in report.registers_to_callsites.items():
                registers_to_callsites[register] |= callsites
            unparsed_callsites |= report.unparsed_callsites

        return RegisterUsageReport(function_name, registers_to_callsites,
                                   unparsed_callsites)


@dataclasses.dataclass
class RegisterUsageReportGroup:
    reports: dict[str, RegisterUsageReport]

    @staticmethod
    def merge(
        groups: list['RegisterUsageReportGroup']
    ) -> Optional['RegisterUsageReportGroup']:
        if len(groups) == 0:
            return None
        reports_by_function = collections.defaultdict(list)
        for group in groups:
            for function, report in group.reports.items():
                reports_by_function[function].append(report)
        return RegisterUsageReportGroup(
            reports={
                function: RegisterUsageReport.merge_reports(reports)
                for function, reports in reports_by_function.items()
            })

    @staticmethod
    def deserialize(data: bytes) -> Optional['RegisterUsageReportGroup']:
        try:
            out = pickle.loads(data)
        except Exception as e:
            log.info(f"Failed to deserialize pickle: {e}")
            return None
        if out is None:
            return None
        if not isinstance(out, RegisterUsageReportGroup):
            raise Exception(
                f"Unpickled object has unexpected type: {type(out)}")
        return out

    def serialize(self) -> bytes:
        return pickle.dumps(self)


class RegisterTokenPattern:

    def __init__(self, pattern: list[str]):
        """Construct a TokenPattern from the given `pattern`.

        Args:
          pattern: A list of token values. Wildcards are represented by None.
        """
        self._pattern = pattern

    def count_wildcards(self):
        return len([w for w in self._pattern if w is None])

    def find_matches(self, tokens: list[str]) -> Optional[list[str]]:
        """Process the given tokens and return all matches.

        Args:
          tokens: A non-empty list of token values. No wildcards are allowed.
        """
        assert [t for t in tokens if t is not None]

        if len(tokens) != len(self._pattern):
            return None

        out = []

        for t, p in zip(tokens, self._pattern):
            if p is None:  # The wildcard matches any token.
                out.append(t)
            elif t != p:  # Non-wildcards must be exact matches.
                return None

        return out

    @staticmethod
    def find_first_match(
            patterns: list['RegisterTokenPattern'], tokens: list[str],
            function_name: str,
            call_site: clang.cindex.Cursor) -> RegisterUsageReport:
        for pattern in patterns:
            report = RegisterUsageReport(
                function_name=function_name,
                registers_to_callsites=collections.defaultdict(set),
                unparsed_callsites=set())

            matches = pattern.find_matches(tokens)
            if matches is None:
                continue
            assert len(matches) == pattern.count_wildcards()

            extent = SingleFileSourceRange.from_source_range(call_site.extent)
            print("--", function_name)
            print(extent.preview())

            if len(matches) > 0:
                for match in matches:
                    report.registers_to_callsites[match].add(extent)
            elif pattern.count_wildcards() == 0:
                report.unparsed_callsites.add(extent)
            return report

        raise Exception("No pattern matched tokens at call-site for " +
                        f"{call_site.displayname}: {tokens}")


@functools.cache
def _walk_callsites(cursor: clang.cindex.Cursor,
                    function_name: str) -> list[clang.cindex.Cursor]:
    """Preorder walk over `cursor` that selects call-sites of `function-name`.

    This is likely the most expensive operation in a program that uses
    CallSiteAnalyzer, so it's worth memoizing.
    """
    out = []
    for cursor in cursor.walk_preorder():
        if cursor.kind != clang.cindex.CursorKind.CALL_EXPR:
            continue
        if cursor.displayname != function_name:
            continue
        print("Function call to '{}' found at {}:{}:{}".format(
            cursor.spelling, cursor.location.file, cursor.location.line,
            cursor.location.column))
        out.append(cursor)
    return out


class CallSiteAnalyzer:

    def __init__(self, function_name: str, arg_index: int,
                 reg_token_patterns: list[RegisterTokenPattern]):
        """Create a call-site analyzer for a given function.

        Token semantics:

          The list of tokens patterns is intended to be complete. If we ever
          hit a call site for the given function that does not match any of the
          token patterns, we will raise an exception.

          None values in a token pattern are interpreted as wildcards. They
          should only be used to match register offsets. If there is no
          wildcard, call sites will be filed in the report as items for human
          review.

        Args:
          function_name: The function whose call sites we wish to analyze.

          arg_index: The index of the argument we wish to pattern-match.

          reg_token_patterns: A list of token patterns to match with. If the
            list of token patterns is incomplete, `CallSiteAnalyzer.run()` will
            raise an exception.


        The list of token patterns where None is a stand-in for
        a register offset. If the list of token patterns is incomplete, we will
        intentionally raise an uncaught exception in order to fail the Bazel
        build.

        """
        self.function_name = function_name
        self._patterns = reg_token_patterns
        self._arg_index = arg_index

    def run(self,
            cursor: clang.cindex.Cursor) -> Optional[RegisterUsageReport]:
        """Analyze all relevant call-sites under `cursor`.

        Returns the result of merging the reports generated for each call-site.
        If no reports were generated, returns None.
        """
        reports: list[RegisterUsageReport] = []

        for cursor in _walk_callsites(cursor, self.function_name):
            args_tokens: list[list[str]] = []
            arg: clang.cindex.Cursor
            for i, arg in enumerate(cursor.get_arguments()):
                tokens = [t.spelling for t in arg.get_tokens()]
                args_tokens.append(tokens)

            assert self._arg_index < len(args_tokens)
            tokens = args_tokens[self._arg_index]
            # It would be surprising if any tokens produced by libclang were
            # None or empty strings.
            assert all(tokens), f"Each token should be truthy: {tokens}"

            # It would be nice to assert that `len(tokens) > 0` since we are
            # only analyzing functions that have parameters, but this property
            # doesn't seem to hold when the function's call site is lost by a
            # macro, e.g. `OT_DISCARD(foo(1))` would give us `tokens == [[]]`.
            if len(tokens) == 0:
                continue

            report = RegisterTokenPattern.find_first_match(
                self._patterns, tokens, cursor.displayname, cursor)
            reports.append(report)

        return RegisterUsageReport.merge_reports(reports)
