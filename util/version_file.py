#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys


def parse_version_file(path):
    """
    Parse a bazel version file and return a dictionary of the values.
    If `path` is None, an empty dictionary is returned.
    If an error occurs during parsing, an exception is raised.
    """
    if path is None:
        return {}
    version_stamp = {}
    try:
        with open(path, 'rt') as f:
            for line in f:
                k, v = line.strip().split(' ', 1)
                version_stamp[k] = v
    except ValueError:
        raise SystemExit(sys.exc_info()[1])
    return version_stamp
