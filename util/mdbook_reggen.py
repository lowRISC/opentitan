#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that generates interface and register tables for ip blocks.

The preprocessor finds ip configs in SUMMARY.md and converts them into a html document
with tables for hardware interfaces and registers.
"""

import json
import sys
import re
import io
from pathlib import Path
from typing import List

from mdbook import utils as md_utils
from reggen.ip_block import IpBlock
import reggen.gen_cfg_md as gen_cfg_md
import reggen.gen_md as gen_md

REGREF_PATTERN = re.compile(r"\{\{#regref\s+?(.+?)\s*?\}\}")


def main() -> None:
    md_utils.supports_html_only()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)
    book_root = context["root"]

    try:
        ip_cfg_str = context["config"]["preprocessor"]["reggen"][
            "ip-cfg-py-regex"]
        ip_cfg_pattern = re.compile(ip_cfg_str)
    except KeyError:
        sys.exit(
            "No RegEx pattern given in book.toml to identify ip block configuration files.\n"
            "Provide regex as preprocessor.reggen.ip-cfg-py-regex .", )

    cfg_files: List[Path] = []
    for chapter in md_utils.chapters(book["sections"]):
        src_path = chapter["source_path"]
        if not src_path or not ip_cfg_pattern.search(src_path):
            continue

        block = IpBlock.from_text(
            chapter["content"], [],
            "file at {}/{}".format(context["root"], chapter["source_path"]))
        buffer = io.StringIO()
        buffer.write("# Hardware Interfaces\n")
        gen_cfg_md.gen_cfg_md(block, buffer)

        buffer.write("# Registers\n")
        gen_md.gen_md(block, buffer)
        chapter["content"] = buffer.getvalue()

        cfg_files.append(Path(src_path))

    for chapter in md_utils.chapters(book["sections"]):
        if not chapter["source_path"]:
            continue
        src_dir = Path(chapter["source_path"]).parent

        chapter["content"] = md_utils.change_link_ext(
            cfg_files,
            chapter["content"],
            ".html",
            book_root,
            src_dir,
        )

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
