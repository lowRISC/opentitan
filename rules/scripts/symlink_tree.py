#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import os.path
import stat
import sys

parser = argparse.ArgumentParser(description='Symlink Tree Creator')
parser.add_argument('SRC', help='Source directory')
parser.add_argument('DST',
                    help='Destination directory (location of symlink tree)')


class SymlinkTree(object):

    def __init__(self, src):
        if not os.path.exists(src):
            raise FileNotFoundError(src)
        self.src = src
        # Inventory of original paths to destination-relative paths
        self.inventory = {}
        # Extra symlinks to create (e.g. directory symlinks)
        self.extra_links = {}

    def _symlink(self, src, dst):
        if os.path.lexists(dst):
            os.remove(dst)
        os.symlink(src, dst)

    def link(self, dst):
        os.makedirs(dst, exist_ok=True)
        for (root, dirs, files) in os.walk(self.src):
            rel = os.path.relpath(root, self.src)
            real = os.path.realpath(root)
            dpath = os.path.join(dst, rel)

            self.inventory[real] = rel
            # Make a subdir for this root within the src walk
            os.makedirs(dpath, exist_ok=True)

            # Look for any dir symlinks within the dirs and remember them.
            for d in dirs:
                orig = os.path.join(root, d)
                new = os.path.join(rel, d)
                st = os.stat(orig, follow_symlinks=False)
                if stat.S_ISLNK(st.st_mode):
                    self.extra_links[new] = os.path.realpath(orig)

            # For each file, create a symlink to the original
            for f in files:
                orig = os.path.join(real, f)
                new = os.path.join(dpath, f)
                self._symlink(orig, new)

        # Now, for "directory" symlinks, resolve and create new links
        for (new, orig) in self.extra_links.items():
            if orig in self.inventory:
                # Symlink points within the src tree and should go to a newly
                # created directory.
                orig = os.path.realpath(os.path.join(dst,
                                                     self.inventory[orig]))
                new = os.path.join(dst, new)
                self._symlink(orig, new)
            else:
                # Symlink points elsewhere and should be linked directly.
                new = os.path.realpath(new)
                self._symlink(orig, new)


def main():
    args = parser.parse_args()
    tree = SymlinkTree(args.SRC)
    tree.link(args.DST)
    return 0


if __name__ == '__main__':
    sys.exit(main())
