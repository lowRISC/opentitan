#!/usr/bin/env python3
# Copyright lowRISC contributors.
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

from mdbook import utils as md_utils
from reggen.ip_block import IpBlock
import reggen.gen_cfg_html as gen_cfg_html
import reggen.gen_html as gen_html

REGREF_PATTERN = re.compile(r"\{\{#regref\s+?(.+?)\s*?\}\}")


def main() -> None:
    md_utils.supports_html_only()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)
    book_root = context["root"]

    try:
        ip_cfg_str = context["config"]["preprocessor"]["reggen"]["ip-cfg-py-regex"]
        ip_cfg_pattern = re.compile(ip_cfg_str)
    except KeyError:
        sys.exit(
            "No RegEx pattern given in book.toml to identify ip block configuration files.\n"
            "Provide regex as preprocessor.reggen.ip-cfg-py-regex .",
        )

    name2path = {}
    for chapter in md_utils.chapters(book["sections"]):
        src_path = chapter["source_path"]
        if not src_path or not ip_cfg_pattern.search(src_path):
            continue

        block = IpBlock.from_text(
            chapter["content"],
            [],
            "file at {}/{}".format(context["root"], chapter["source_path"])
        )
        buffer = io.StringIO()
        buffer.write("# Hardware Interfaces and Registers\n")
        buffer.write("## Interfaces\n")
        gen_cfg_html.gen_cfg_html(block, buffer)
        buffer.write("\n## Registers\n")
        gen_html.gen_html(block, buffer)
        chapter["content"] = buffer.getvalue()

        name2path[block.name] = src_path

    cfg_files = set(Path(p) for p in name2path.values())
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

        def regref_swap(match: re.Match) -> str:
            """Replaces regref with a link to the register."""
            reg = match.group(1).split(".")
            if len(reg) > 3 or len(reg) < 2:
                sys.exit(
                    f"{match.group(0)} is invalid. "
                    "Should be in the form: 'ip_block.register.field', where 'field' is optional.",
                )
            try:
                # Make the path to the config file absolute (to root of the site),
                # so we don't have to worry about what page we are in.
                # Also, do the hjson -> html conversion.
                path = "/{}.html".format(
                    name2path[reg[0]].removeprefix("./").removesuffix(".hjson")
                )
            except KeyError:
                sys.exit(f"Ip block with name '{reg[0]}' could not be found.")

            name = reg[1] + "." + reg[2] if len(reg) == 3 else reg[1]

            return "[`{}`]({}#Reg_{})".format(name, path, reg[1].lower())

        chapter["content"] = REGREF_PATTERN.sub(regref_swap, chapter["content"])

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
