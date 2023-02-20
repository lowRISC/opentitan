#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that adds an overview to linked header files.

This overview holds links to the generated doxygen api documentation
as well as the actual file.
"""
import json
import sys
import io
import re
from pathlib import Path, PurePath

import mdbook
from mdbook import difgen

SRCTREE_TOP = Path(__file__).parents[1].resolve()


def main() -> None:
    mdbook.supports_html_only()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)
    book_root = Path(context["root"])

    try:
        site_url = PurePath(context["config"]["output"]["html"]["site-url"])
    except KeyError:
        site_url = PurePath("/")

    try:
        preproc_cfg = context["config"]["preprocessor"]["doxygen"]
        out_dir = SRCTREE_TOP / preproc_cfg["out-dir"]
        html_out_dir = "/" + preproc_cfg["html-out-dir"]
        dif_src_regex = re.compile(preproc_cfg["dif-src-py-regex"])
    except KeyError:
        sys.exit(
            "mdbook-doxygen requires are set in the book.toml configuration.\n"
            "\tpreprocessor.reggen.out-dir -- Doxygen's output directory.\n"
            "\tpreprocessor.reggen.html-out-dir -- Doxygen's html out directory.\n"
            "\tpreprocessor.reggen.dif-src-py-regex -- A regex for identifying dif files.\n"
        )

    combined_xml = difgen.get_combined_xml(out_dir / 'api-xml')

    header_files = set()
    chapters_gen = mdbook.chapters(book["sections"])
    for chapter in chapters_gen:
        src_path = chapter["source_path"]
        if src_path is None or dif_src_regex.search(src_path) is None:
            continue

        file_name = Path(src_path).name

        # First calculate the path to the generated dif header,
        # relative to the root of the project. This is the form ingested
        # by the difgen library scripts.
        rel_dif_h = (book_root / src_path).relative_to(SRCTREE_TOP)

        buffer = io.StringIO()
        buffer.write(f"# {file_name}\n")
        difgen.gen_listing_html(html_out_dir, combined_xml, str(rel_dif_h), buffer)
        buffer.write(
            "\n<details><summary>\nGenerated from <a href=\"{}\">{}</a></summary>\n".format(
                site_url / src_path,
                file_name,
            ),
        )
        buffer.write("\n```c\n{}\n```\n".format(chapter["content"]))
        buffer.write("</details>")
        chapter["content"] = buffer.getvalue()

        # Rewrite path so `dif_*.h` files don't collide with `dif_*.md` files.
        if Path(chapter["path"]).suffix == ".h":
            chapter["path"] = str(Path(chapter["path"]).with_suffix(""))
        chapter["path"] = chapter["path"] + "_h.html"

        header_files.add(Path(src_path))

    chapters_gen = mdbook.chapters(book["sections"])
    for chapter in chapters_gen:
        if chapter["source_path"] is None:
            continue
        page_path = Path(chapter["source_path"]).parent

        chapter["content"] = mdbook.change_link_ext(
            header_files,
            chapter["content"],
            "_h.html",
            book_root,
            page_path,
        )

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
