#!/usr/bin/env python

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Checks for Bazel targets that contain banned characters.
"""

import sys

from lib.bazel_query import BazelQuery, BazelQueryRunner

AZURE_PIPELINES_ERROR = "##vso[task.logissue type=warning]"

if __name__ == '__main__':
    bazel = BazelQueryRunner()

    DEPRECATED_TAGS = ["vivado"]

    for tag in DEPRECATED_TAGS:
        query = BazelQuery.tag_exact(tag, "//...")
        results = list(bazel.query(query))
        if results:
            print(AZURE_PIPELINES_ERROR, end='')
            print(f"Some targets have a deprecated tag ({tag}):")
        for target in results:
            print(f"Target has tag {tag}: {target}")

    if results:
        sys.exit(1)
