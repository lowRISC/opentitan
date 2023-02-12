#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Replaces front-matter with a standard markdown title, ignoring all other fields"""

from pathlib import Path
import argparse


parser = argparse.ArgumentParser()
parser.add_argument("root_doc",
                    help = "path to the root of documentation")
g_args = parser.parse_args()

g_root_doc = Path(g_args.root_doc).resolve()
# if root doc is a link to a book.toml file, just open this one
assert g_root_doc.is_dir(), "you must give a path to the root of the repo"


def apply_to_md_files(path, fn):
    """
    List all files under the directory of the book and call a function on each one
    """
    def apply_rec(path):
        for child in path.iterdir():
            if child.name.endswith(".md"):
                fn(child)
            if child.is_dir():
                apply_rec(child.resolve())
    apply_rec(path)


def rewrite_title(path):
    relpath = path.relative_to(g_root_doc)
    # don't touch files in site/, sw/vendor/, hw/vendor/
    if relpath.parts[0] == "site" or relpath.parts[0:2] in (('sw', 'vendor'), ('hw', 'vendor')):
        return
    with path.open() as f:
        lines = []
        for line in f:
            lines.append(line)
        # it must start with ---
        if len(lines) == 0 or not lines[0].startswith("---"):
            return  # ignore
        line_nr = 1
        title = None
        while not lines[line_nr].startswith("---"):
            this_line = lines[line_nr]
            line_nr += 1
            if this_line.startswith("title:"):
                title = this_line[6:].strip()
        # remove quotes if any
        if title[0] == '"' and title[-1] == '"':
            title = title[1:-1]
        new_lines = [f"# {title}\n"]
        lines = new_lines + lines[line_nr + 1:]
        path.write_text("".join(lines))


apply_to_md_files(g_root_doc, rewrite_title)
