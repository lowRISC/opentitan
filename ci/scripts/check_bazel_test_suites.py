#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Checks for test_suite targets that are either empty or not tagged "manual".
"""

import sys

from lib.bazel_query import BazelQueryRunner

NON_MANUAL_TEST_SUITE_DESCRIPTION = """
Test suites below aren't tagged with manual, but probably should be.

Without the "manual" tag, these test suites will match wildcards like //... and
may pull in tests that were otherwise excluded with --build_tag_filters. (This
will not happen if the test suites have the same tags as their contents.)

There aren't many scenarios in which you need a test_suite to match wildcards
(because its tests are also in the workspace) so you should probably tag it
with manual.
"""

EMPTY_TEST_SUITE_DESCRIPTION = """
Test suites below contain zero tests. This is probably an accident.
"""

AZURE_PIPELINES_WARNING = "##vso[task.logissue type=error]"
AZURE_PIPELINES_ERROR = "##vso[task.logissue type=warning]"

if __name__ == '__main__':
    bazel = BazelQueryRunner()
    non_manual_test_suites = list(bazel.find_non_manual_test_suites())
    empty_test_suites = list(bazel.find_empty_test_suites())

    if non_manual_test_suites:
        print("-" * 80)
        print(AZURE_PIPELINES_WARNING + NON_MANUAL_TEST_SUITE_DESCRIPTION)
        for target in non_manual_test_suites:
            print("  - " + target)

    if empty_test_suites:
        print("-" * 80)
        print(AZURE_PIPELINES_ERROR + EMPTY_TEST_SUITE_DESCRIPTION)
        for target in empty_test_suites:
            print("  - " + target)

    if empty_test_suites:
        sys.exit(1)
