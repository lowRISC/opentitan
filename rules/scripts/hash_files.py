#!/usr/bin/env python
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Hash all files given as argument.

This script will collect the list of files provided on the command line,
sort it and then hash the content of all files.

When hashing files, both the file name and file contents will be hashed.
It might be convenient to change or even ignore the file name when hashing,
for example if it starts with an unstable prefix. To do so, every file path
containing '@' will be interpreted as '<real path>@<short path>'.
Note that the sorting order uses the <short path> if provided.
"""

import argparse
from pathlib import Path
import hashlib
import sys
from typing import Tuple


def parse_path(path: str) -> Tuple[Path, Path]:
    if '@' in path:
        real_path, hashed_path = path.split('@', maxsplit=1)
        return (Path(real_path), hashed_path)
    else:
        return (Path(path), path)


def print_fname(p: Tuple[Path, Path]):
    # If the real and hashes name are the same, only print the name, otherwise use
    # the same format as the input.
    real = str(p[0])
    hashed = p[1]
    return real if real == hashed else f"{real}@{hashed}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--file-list',
        action='append',
        default=[],
        type=Path,
        help="Read file list to hash from the given file"
    )
    parser.add_argument(
        '--output-list',
        type=Path,
        help='Output sorted list of files to the given file'
    )
    parser.add_argument(
        '--output-hash',
        type=Path,
        help='Output hash to the given file (otherwise to stdout)'
    )
    parser.add_argument('files', type=parse_path, nargs='*', help='Files to hash')
    args = parser.parse_args()

    files = args.files
    # Read the file lists if requested.
    for fl in args.file_list:
        lines = fl.read_text().split('\n')
        paths = list(map(parse_path, filter(None, lines)))
        files.extend(paths)

    # Sort file list (by hashed path)
    files.sort(key = lambda p: p[1])

    # If required, output the sorted file list.
    if args.output_list:
        args.output_list.write_text('\n'.join(map(print_fname, files)))

    # Hash the files.
    h = hashlib.sha1()
    for p in files:
        # Hash the file name, followed by the content.
        h.update(p[1].encode())
        h.update(p[0].read_bytes())

    # Produce digest.
    digest = h.hexdigest()
    if args.output_hash:
        args.output_hash.write_text(digest)
    else:
        print(digest)


if __name__ == "__main__":
    sys.exit(main())
