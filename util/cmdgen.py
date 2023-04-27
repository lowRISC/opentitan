#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Mechanism to auto-generate documentation based on inline shell commands.

This is a generic, repeatable method of inserting generated/rendered content
into a markdown file. The populated .md file can then be committed into the
repository, so the in-repo representation matches the generated content.

CI tooling can automatically re-generate the files if other changes to the
repository would change the generated content. Linting or pre-commit checks
could keep such-documenation always up-to-date.
"""

import sys
from pathlib import Path
import re
import subprocess
import argparse

import logging
logger = logging.getLogger(__name__)


# START and END marker tags use the HTML-style comments '<!-- -->'
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


def cmdgen_rewrite_md(filepath: Path, dry_run: bool):
    '''Find all matching blocks in a file, and re-generate their contents.

    START_MARKER_PATTERN and END_MARKER_PATTERN define the delimiters.
    For example, CMDGEN blocks are defined within a file as follows...
    """
    <!-- BEGIN CMDGEN util/selfdoc.py reggen -->
                       `--------------------`
                                `cmd`

    ...generated_content...


    <!-- END CMDGEN -->
    """

    '''
    content = filepath.read_text()
    modified = False
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
            sys.exit(f"Error in {filepath}: start marker on "
                     f"L{match_start_linum} with command '{cmd}' is missing a"
                     "matching end marker!")

        logger.info(f" {filepath}:L{match_start_linum} : Running cmd '{cmd}'")
        if dry_run:
            # don't run
            pos = match_end.end(0)
            continue

        # Run the found-command in a subshell
        res = subprocess.run(cmd, shell=True, capture_output=True)
        if res.stderr:
            logger.info(f"At L{match_start_linum} the command '{cmd}' output"
                        " the following error messages:\n"
                        f" {res.stderr.decode()}")
        if res.returncode != 0:
            sys.exit(f"At L{match_start_linum} the command '{cmd}' had a"
                     " non-zero return code.")

        new_content = res.stdout.decode()
        # replace content
        content = \
            content[0:match_start.end(0)] + \
            '\n' + new_content + '\n' + \
            content[match_end.start(0):]
        modified = True
        # resume after end line, adjust for new content size
        pos = \
            match_end.end(0) + \
            len(new_content) - \
            (match_end.start(0) - match_start.end(0))

    # write back
    if modified:
        filepath.write_text(content)


def main():
    '''Run CMDGEN for all markdown files in the OpenTitan project.'''
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run",
                        help="Print commands but do not execute",
                        action="store_true")
    args = parser.parse_args()

    logging.basicConfig()
    logging.getLogger().setLevel(logging.DEBUG)  # root -> most-permissive
    logger.setLevel(logging.INFO)

    repo_root = Path(__file__).parents[1].resolve()
    for f in repo_root.rglob('**/*.md'):  # Recursively find all .md files
        cmdgen_rewrite_md(f, args.dry_run)


if __name__ == '__main__':
    main()
