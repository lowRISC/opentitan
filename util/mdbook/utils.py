# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Common utilities used by mdbook pre-processors."""

import sys
import re
from os import path
from typing import List, Any, Dict, Generator, Set
from pathlib import Path

LINK_PATTERN_STR = r"\[(.*?)\]\(([^#\?\)]*)(.*?)\)"
LINK_PATTERN = re.compile(LINK_PATTERN_STR)


def change_link_ext(
        file_list: Set[Path],
        content: str,
        new_suffix: str,
        book_root: Path,
        page_path: Path,
) -> str:
    def suffix_swap(match: re.Match) -> str:
        """Swaps the extension of the file being linked to if it is a ip block config."""
        try:
            # relative_to can fail with a value error, if it isn't a local link
            book_relative_path = (page_path / match.group(2)).resolve().relative_to(book_root)
        except ValueError:
            return match.group(0)

        if book_relative_path in file_list:
            return "[{}]({}{}{})".format(
                match.group(1),
                path.splitext(match.group(2))[0],
                new_suffix,
                match.group(3),
            )
        else:
            return match.group(0)

    return LINK_PATTERN.sub(suffix_swap, content)


def supports_html_only() -> None:
    if len(sys.argv) > 2:
        if (sys.argv[1], sys.argv[2]) == ("supports", "html"):
            sys.exit(0)
        else:
            sys.exit(1)


def chapters(items: List[Dict[str, Any]]) -> Generator[Dict[str, Any], None, None]:
    """Recursively yields all chapters"""
    for chapter in (item.get("Chapter") for item in items):
        if not chapter:
            continue

        for sub_chapter in chapters(chapter["sub_items"]):
            yield sub_chapter

        yield chapter
