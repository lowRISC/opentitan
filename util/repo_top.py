#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Library to find the path to the repository's top.'
"""

from pathlib import Path


def repo_top() -> Path:
    top = Path(__file__).resolve().parents[1]
    assert (top / "util").exists(), "something is wrong with repository's top detection"
    return top
