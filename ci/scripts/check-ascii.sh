#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Check that there are no "source" files in the repository that
# contain non-ASCII characters.

set -e

# Suffixes of files that are allowed to contain non-ASCII characters.
# These obviously include non-text files, but we also include .md and
# .html because we've used non-ASCII encoding in quite a few of them
# to make documentation easier to write.
allowed_suffixes=(
    png
    ico
    bin
    der
    vsdx
    elf

    md
    html

    # The ECMA Script standard allows unicode:
    # https://262.ecma-international.org/6.0/#sec-source-text
    #
    # There is no OpenTitan JavaScript style guide so all `js`
    # have not been white listed.
    #
    # However, minified Javascript is similar to executables
    # in that it is not edited directly
    # but produced by a compiler/minifier for a JavaScript run-time,
    # and so it makes sense for it to be excluded from this ascii check.
    min.js

    # We don't mandate 7-bit ASCII for Python or C/C++ code. The
    # Google style guide, which we inherit suggests avoiding
    # unnecessary non-ASCII text, but doesn't forbid it entirely.
    py
    c
    cc
    h
    hh
)
suff_re=""
for suff in "${allowed_suffixes[@]}"; do
    suff_re="${suff_re}${suff}\\|"
done
suff_re="\\.\\(${suff_re:0:-2}\\)$"

# Other paths that should be excluded from the check. This includes
# vendored files (that we don't control) and other binary files
# without a suffix or non-source files.
excl_paths=(
    '.*/vendor/.*'
    COMMITTERS
    hw/ip/usbdev/pmod/tusb1106pmod-kicad/fp-info-cache
    site/landing/data/partner_quotes.json
)
excl_re=""
for excl in "${excl_paths[@]}"; do
    excl_re="${excl_re}${excl}\\|"
done
excl_re="^\\(${excl_re:0:-2}\\)$"

TMPFILE="$(mktemp)" || {
    echo >&2 "Failed to create temporary file"
    exit 1
}
trap 'rm -f "$TMPFILE"' EXIT

git ls-files | \
    grep -v "${excl_re}" | \
    grep -v "${suff_re}" | \
    env LC_ALL=C xargs grep -d skip -P '[^\0-\x7f]' >"$TMPFILE" || true
if [ -s "$TMPFILE" ]; then
    echo -n "##vso[task.logissue type=error]"
    echo "One or more files have unexpected non-ASCII text:"
    cat "$TMPFILE"
    exit 1
fi
