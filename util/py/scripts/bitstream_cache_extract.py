#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
import tarfile

from pathlib import Path

"""
Creates bitstreams cache directory entry from a bitstream archive.
The archive must have been created by a bazel target such as
//hw/bitstream:chip_earlgrey_cw340_cached_archive
or
//hw/bitstream/vivado:earlgrey_cw340_archive
"""

parser = argparse.ArgumentParser(
    description='Bitstream Cache Entry Extractor')
parser.add_argument('--cache', required=True, type=Path, help='Path to the bitstream cache')
parser.add_argument('--replace', action="store_true",
                    help='When set, existing cache entries with the same name are replaced')
parser.add_argument('entry_name', help='Name of the cache entry to create')
parser.add_argument('archive', type=Path, help='Path to bitstream archive')


def main(argv: list[str]):
    args = parser.parse_args(args=argv[1:])

    # Sanity checks on the input.
    assert args.cache.exists() and args.cache.is_dir(), \
        "the cache directory must already exists"
    args.cache = args.cache / "cache"
    assert args.cache.exists() and args.cache.is_dir(), \
        "the cache directory must contain a 'cache' sub-directory"
    assert args.archive.exists() and args.archive.is_file(), \
        "the bitstream archive must be an existing file"

    # Make sure that the request entry does not already exists and create a directory.
    entry_dir = args.cache / args.entry_name
    if not args.replace:
        assert not entry_dir.exists(), \
            f"the bitstream cache already contains the entry '{args.entry_name}', " + \
            "either remove it or use --replace"
    entry_dir.mkdir(exist_ok=True)

    # Try to open the bitstream archive (tarfile handles compression transparently).
    try:
        archive = tarfile.open(args.archive)
    except tarfile.TarError as e:
        print("cannot open bitstream archive:")
        print(e)
        sys.exit(1)

    # The archive typically does not contain the manifest.json file at the root.
    # Find the prefix to strip to reach the manifest.
    manifest_dir = None
    for entry in archive:
        entry = Path(entry.name)
        if Path(entry.name).name == "manifest.json":
            manifest_dir = entry.parent
    if not manifest_dir:
        print("the bitstream archive does not contain any manifest")
        sys.exit(1)

    # Now extract the bitstream archive to the cache.
    def extract_filter(info, path):
        info = tarfile.data_filter(info, path)
        if not info:
            return None
        entry = Path(info.name)
        # Ignore entries which are not in a sub-directory of the manifest's directory.
        if not entry.is_relative_to(manifest_dir):
            # Only print an error message for files (directories produce noise).
            if not info.isdir():
                print(f"ignoring entry {entry} which is not in a sub-directory " +
                      f" of the manifest ({manifest_dir})")
            return None
        info.name = entry.relative_to(manifest_dir)
        return info

    archive.extractall(entry_dir, filter=extract_filter)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
