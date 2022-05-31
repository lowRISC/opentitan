#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# fix_trailing_whitespace.py script ensures that all files passed into it satisfy
# various requirements in terms of whitespace:
# - There is no leading whitespace in the file.
# - Lines do not have trailing non-newline whitespace and have UNIX-style line endings.
# - The file ends in a single newline.

import argparse
import sys
import subprocess

from pathlib import Path

# This file is $REPO_TOP/util/fix_trailing_newlines.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


def is_ignored(path):
    return subprocess.run(['git', 'check-ignore', path]).returncode == 0


def walk_tree(paths=[REPO_TOP]):
    for path in paths:
        if isinstance(path, str):
            path = Path(path)

        if path.is_symlink() or is_ignored(path) or 'LICENSE' in path.parts:
            continue

        if path.is_dir() and 'vendor' not in path.parts:
            yield from walk_tree(path.iterdir())
        else:
            yield path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='report writes which would have happened')
    parser.add_argument(
        '--recursive', '-r',
        action='store_true',
        default=False,
        help='traverse the entire tree modolo .gitignore'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='verbose output')
    parser.add_argument(
        'files',
        type=str,
        nargs='*',
        help='files to fix whitespace for')
    args = parser.parse_args()

    files = args.files
    if args.recursive:
        files = walk_tree(args.files)

    total_fixable = 0
    for path in files:
        path = Path(path).resolve().relative_to(REPO_TOP)
        if not path.is_file() or path.is_symlink():
            continue
        if 'vendor' in path.parts or path.suffix in ['.patch', '.svg', '.tpl']:
            continue
        if args.verbose:
            print(f'Checking: "{path}"')

        try:
            old_text = path.read_text()
        except UnicodeDecodeError:
            print(f'Binary file: "{path}"')
            continue
        new_text = "\n".join([line.rstrip() for line in old_text.strip().split("\n")]) + "\n"

        if old_text != new_text:
            print(f'Fixing file: "{path}"', file=sys.stdout)
            total_fixable += 1
            if not args.dry_run:
                path.write_text(new_text)

    if total_fixable:
        verb = 'Would have fixed' if args.dry_run else 'Fixed'
        print(f'{verb} {total_fixable} files.', file=sys.stderr)

    # Pass if we fixed everything or there was nothing to fix.
    return 1 if total_fixable > 0 else 0


if __name__ == '__main__':
    sys.exit(main())
