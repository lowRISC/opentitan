#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that generates testplans for the ip blocks.

The preprocessor finds testplans in SUMMARY.md and converts them into a html document.
"""

import json
import sys
import re
import io
from pathlib import Path

from mdbook import utils as md_utils
import dvsim.Testplan as Testplan


def main() -> None:
    md_utils.supports_html_only()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)
    book_root = Path(context["root"])

    try:
        testplan_str = context["config"]["preprocessor"]["testplan"]["testplan-py-regex"]
        testplan_pattern = re.compile(testplan_str)
    except KeyError:
        sys.exit(
            "No RegEx pattern given in book.toml to identify testplan files.\n"
            "Provide regex as preprocessor.testplan.testplan-py-regex .",
        )

    testplan_files = set()
    for chapter in md_utils.chapters(book["sections"]):
        src_path = chapter["source_path"]
        if not src_path or not testplan_pattern.search(src_path):
            continue
        # Testplan prints to stdout, redirect that to stderr for error messages
        from contextlib import redirect_stdout
        with redirect_stdout(sys.stderr):
            plan = Testplan.Testplan(
                book_root / chapter["source_path"],
                repo_top = book_root)
            buffer = io.StringIO()
            buffer.write(plan.get_testplan_table("html"))
            chapter["content"] = buffer.getvalue()

        testplan_files.add(Path(chapter["source_path"]))

    for chapter in md_utils.chapters(book["sections"]):
        if not chapter["source_path"]:
            continue
        src_dir = Path(chapter["source_path"]).parent

        chapter["content"] = md_utils.change_link_ext(
            testplan_files,
            chapter["content"],
            ".html",
            book_root,
            src_dir,
        )

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
