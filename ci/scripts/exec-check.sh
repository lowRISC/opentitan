#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Find executable files that should not be executable.

set -e

# Files with these extensions may be executable.
allowed_extensions=(
    py
    sh
)

# Arguments for `find`.
args=(
    # Do not look in these directories.
    -name .git -prune -o
    -name vendor -prune -o
    -name scratch -prune -o
    -name build-site -prune -o
    # Filter to executable files.
    -type f
    -executable
    # Filter to files with extensions.
    -name '*.*'
)

# Filter out files with allowed extensions.
for ext in "${allowed_extensions[@]}"; do
    args+=(-not -name "*.${ext}")
done

# Find the names of bad files.
bad_files=$(find . "${args[@]}" -print)

# Fail if any exist.
if [ -n "$bad_files" ]; then
    echo -n "##vso[task.logissue type=error]"
    echo "The following files should not have their executable bit set:" >&2
    echo "$bad_files" >&2
    exit 1
fi
