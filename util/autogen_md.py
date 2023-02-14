#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Go through all markdown files and autogenerate content based on commands
recorded in the file.
"""

import sys
from pathlib import Path
import re
import subprocess
import argparse
import os
from typing import Callable

START_MARKER_PATTERN = re.compile(r"\n<!--\s*BEGIN\s*AUTOGEN\s*(?P<cmd>.+)\s*-->\n")
END_MARKER_PATTERN = re.compile(r"\n<!--\s*END\s*AUTOGEN\s*-->\n")


def apply_to_all_files(path: Path, fn: Callable[[Path], None]):
    for child in path.iterdir():
        if child.is_file():
            fn(child)
        if child.is_dir():
            apply_to_all_files(child, fn)


def autogen_rewrite_md(filepath: Path, dry_run: bool):
    # only consider .md files
    if not filepath.name.endswith(".md"):
        return
    content = filepath.read_text()
    modified = False
    pos = 0
    while True:
        # search next start marker
        match_start = START_MARKER_PATTERN.search(content, pos)
        if match_start is None:
            # no more replacements to do
            break
        cmd = match_start.group('cmd').strip()
        # search end marker after the start marker
        match_end = END_MARKER_PATTERN.search(content, pos)
        if match_end is None:
            sys.exit(f"Error in {filepath}: start marker with command '{cmd}' without end marker")

        print(f"In {filepath}: running '{cmd}'")
        if dry_run:
            # don't run
            pos = match_end.end(0)
            continue
        res = subprocess.run(cmd, shell=True, capture_output=True)
        if res.stderr:
            print(
                f"The command '{cmd}' output "
                f"the following error messages:\n{res.stderr.decode()}"
            )
        if res.returncode != 0:
            sys.exit(f"The command '{cmd}' had a non-zero return code.")

        new_content = res.stdout.decode()
        # replace content
        content = content[0:match_start.end(0)] + new_content + content[match_end.start(0):]
        modified = True
        # resume after end line, adjust for new content size
        pos = match_end.end(0) + len(new_content) - (match_end.start(0) - match_start.end(0))
    # write back
    if modified:
        filepath.write_text(content)


def main(args: argparse.Namespace):
    this_file_path = Path(__file__)
    repo_root = this_file_path.parent.parent.resolve()
    os.chdir(repo_root)
    apply_to_all_files(repo_root, lambda x: autogen_rewrite_md(x, args.dry_run))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run",
                        help = "print commands to execute but do not execute them",
                        action="store_true")
    args = parser.parse_args()
    main(args)
