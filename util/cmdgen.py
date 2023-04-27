#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Mechanism to auto-generate documentation based on inline shell commands.

This is a generic, repeatable method of inserting generated/rendered content
into documentation files. The populated files can then be committed into the
repository, so the in-repo representation matches the generated content.

CMDGEN blocks are declared within a file as follows:
```
<!-- BEGIN CMDGEN util/selfdoc.py reggen -->
                   `--------------------`
                            `cmd`

... generated_content ...

<!-- END CMDGEN -->
```

CI tooling can automatically check that files are out of date due to
changes to the repository from which the documentation is generated.
"""

import sys
from pathlib import Path
import re
import subprocess
import argparse

import logging
logger = logging.getLogger(__name__)

REPO_ROOT = Path(__file__).parents[1].resolve()

# The CMDGEN block delimiters:
START_MARKER_PATTERN = re.compile(
    r"""^<!--            \s*
        BEGIN \s* CMDGEN \s*
        (?P<cmd>.+)      \s* # The command to generate content
        -->$""",
    flags=(re.M | re.X))
END_MARKER_PATTERN = re.compile(
    r"""^<!--            \s*
        END \s* CMDGEN   \s*
        -->$""",
    flags=(re.M | re.X))


def cmdgen_rewrite_md(filepath: Path, dry_run: bool, update: bool) -> bool:
    '''Find all CMDGEN blocks in a file and check their content is up to date.

    See this module's docstring to see how these blocks are declared.

    Args:
        filepath (Path): The file to check.
        dry_run (bool): If set, commands will be printed, but not executed.
        update (bool): If set, when content is out of date it will be updated.

    Returns:
        bool: If neither dry_run or update are set, will return True if an update is required.
    '''
    rel_path = filepath.relative_to(REPO_ROOT)
    modified = False
    needs_updating = False
    content = filepath.read_text()
    pos = 0
    while True:
        # search next start marker
        match_start = START_MARKER_PATTERN.search(content, pos)
        if match_start is None:
            break  # no more replacements to do
        match_start_linum = 1 + content[0:match_start.start(0)].count("\n")
        cmd = match_start.group('cmd').strip()

        # search end marker after the start marker
        match_end = END_MARKER_PATTERN.search(content, pos)
        if match_end is None:
            sys.exit(
                f"Error in {rel_path}: start marker on L{match_start_linum} "
                "missing a matching end marker!"
            )

        if dry_run:
            logger.info(f"{rel_path}:L{match_start_linum}: `{cmd}`")
            # don't run
            pos = match_end.end(0)
            continue

        # Run the found-command in a subshell
        res = subprocess.run(cmd, shell=True, capture_output=True)
        if res.stderr:
            logger.info(
                f"{rel_path}:L{match_start_linum}: `{cmd}` "
                f"output the following error messages:\n{res.stderr.decode()}"
            )
        if res.returncode != 0:
            sys.exit(
                f"{rel_path}:L{match_start_linum}: `{cmd}` "
                "had a non-zero return code of {res.returncode}."
            )

        pos = match_end.end(0)

        new_content = '\n' + res.stdout.decode() + '\n'
        old_content = content[match_start.end(0):match_end.start(0)]
        if new_content != old_content:
            if update:
                logger.info(
                    f"{rel_path}:L{match_start_linum}: Updating generated content."
                )
                # replace content
                content = \
                    content[0:match_start.end(0)] + \
                    new_content + \
                    content[match_end.start(0):]
                modified = True
                # update position to account for new content size
                pos += len(new_content) - len(old_content)
            else:
                logger.info(
                    f"{rel_path}:L{match_start_linum}: Generated content needs updating."
                )
                needs_updating = True

    # write back
    if modified:
        filepath.write_text(content)

    return needs_updating


def main() -> int:
    '''Either check or update all CMDGEN blocks found in the given files.'''
    parser = argparse.ArgumentParser(prog="cmdgen")
    parser.add_argument(
        "globs", nargs="+", type=str, metavar="file",
        help="File(s) to check with paths relative to the repository root, "
             "these can be given as glob patterns.",
    )
    parser.add_argument(
        "--dry-run", help="Print commands but do not execute.", action="store_true",
    )
    parser.add_argument(
        "-u", "--update", help="Update out of date content.", action="store_true",
    )
    args = parser.parse_args()

    logging.basicConfig()
    logging.getLogger().setLevel(logging.DEBUG)  # root -> most-permissive
    logger.setLevel(logging.INFO)

    needs_updating = False
    for glob in args.globs:
        for file in REPO_ROOT.glob(glob):
            needs_updating |= cmdgen_rewrite_md(file, args.dry_run, args.update)

    return 1 if needs_updating else 0


if __name__ == '__main__':
    exit(main())
