#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

noexec_suffixes=(
    c
    cc
    core
    h
    sv
    tpl
)

suff_re=""
for suff in "${noexec_suffixes[@]}"; do
    suff_re="${suff_re}$suff\\|"
done
suff_re="\\(${suff_re:0:-2}\\)"

path_re=".*\\.${suff_re}$"

TMPFILE="$(mktemp)" || {
    echo >&2 "Failed to create temporary file"
    exit 1
}
trap 'rm -f "$TMPFILE"' EXIT

find -name vendor -prune -o \
     -type f -executable -regex "$path_re" -print >"$TMPFILE"
if [ -s "$TMPFILE" ]; then
    echo -n "##vso[task.logissue type=error]"
    echo "One or more files have the executable bit set when they shouldn't."
    cat "$TMPFILE"
    exit 1
fi
