# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Common utilities used by mdbook pre-processors."""

from typing import List, Any, Dict, Generator


def chapters(items: List[Dict[str, Any]]) -> Generator[Dict[str, Any], None, None]:
    """Recursively yields all chapters"""
    for chapter in (item.get("Chapter") for item in items):
        if not chapter:
            continue

        for sub_chapter in chapters(chapter["sub_items"]):
            yield sub_chapter

        yield chapter
