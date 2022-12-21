#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Checks for Bazel targets that contain banned characters.
"""

import sys

from lib.bazel_query import BazelQueryRunner

AZURE_PIPELINES_ERROR = "##vso[task.logissue type=warning]"

if __name__ == '__main__':
    bazel = BazelQueryRunner()

    results = list(bazel.find_targets_with_banned_chars())
    if results:
        print(AZURE_PIPELINES_ERROR +
              "Some target names have banned characters.")
    for target, bad_chars in results:
        print("Target name contains banned characters {}: {}".format(
            bad_chars, target))

    if results:
        sys.exit(1)
