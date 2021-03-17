#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# fix_include_guard.py script takes any number of C or C++ header files as
# input, and formats their include guards to conform to the style mandated
# by Google C++. See
# https://google.github.io/styleguide/cppguide.html#The__define_Guard
#
# clang-format does not, unfortunately, have support for automatically
# generating the correct include guards; hence the existence of this script.
#
# This script will write the names of all affected files to stdout; if no such
# output is present, all files have the correct guards. This script is
# idempotent. If it cannot fix a file, the script will write the file name to
# stderr and will exit at the end with a nonzero status code.

import argparse
import sys
import re

from pathlib import Path

PROJECT_NAME = "OPENTITAN"

# This file is $REPO_TOP/util/fix_include_guard.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='report writes which would have happened')
    parser.add_argument(
        'headers',
        type=str,
        nargs='+',
        help='headers to fix guards for')
    args = parser.parse_args()

    total_unfixable = 0
    total_fixable = 0

    for header_path in args.headers:
        header = Path(header_path).resolve().relative_to(REPO_TOP)
        if header.suffix != '.h' or 'vendor' in header.parts:
            continue

        uppercase_dir = re.sub(r'[^\w]', '_', str(header.parent)).upper()
        uppercase_stem = re.sub(r'[^\w]', '_', str(header.stem)).upper()
        guard = '%s_%s_%s_H_' % (PROJECT_NAME, uppercase_dir, uppercase_stem)

        header_text = header.read_text()
        header_original = header_text

        # Find the first non-comment, non-whitespace line in the file
        first_line_match = re.search(r'^\s*([^/].*)', header_text, re.MULTILINE)
        if first_line_match is None:
            total_unfixable += 1
            print('No non-comment line found in `{}\'.'.format(header),
                  file=sys.stderr)
            continue

        first_line = first_line_match.group(1).rstrip()

        # Find the old guard name, which will be the first #ifndef in the file.
        # This should be an #ifndef line. If it isn't, we can't fix things
        ifndef_match = re.match(r'#ifndef\s+(\w+)$', first_line)
        if ifndef_match is None:
            total_unfixable += 1
            print('Unsupported first non-comment line in `{}\': {!r}.'
                  .format(header, first_line),
                  file=sys.stderr)
            continue

        old_guard = ifndef_match.group(1)

        # Fix the guards at the top, which are guaranteed to be there.
        header_text = re.sub('#(ifndef|define) +%s' % (old_guard, ),
                             r'#\1 %s' % (guard, ), header_text)

        # Fix up the endif. Since this is the last thing in the file, and it
        # might be missing the comment, we just truncate the file, and add on
        # the required guard end.
        header_text = header_text[:header_text.rindex('#endif')]
        header_text += "#endif  // %s\n" % (guard, )

        if header_text != header_original:
            print('Fixing header: "%s"' % (header, ), file=sys.stdout)
            total_fixable += 1
            if not args.dry_run:
                header.write_text(header_text)

    if total_fixable:
        verb = 'Would have fixed' if args.dry_run else 'Fixed'
        print('{} {} files.'.format(verb, total_fixable), file=sys.stderr)
    if total_unfixable:
        print('Failed to fix {} files.'.format(total_unfixable),
              file=sys.stderr)

    # Pass if we fixed everything or there was nothing to fix.
    unfixed = total_unfixable + (total_fixable if args.dry_run else 0)
    return 1 if unfixed else 0


if __name__ == '__main__':
    sys.exit(main())
