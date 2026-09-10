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

# Drop any paths that git ignores (e.g. a local .venv or build output) so a
# local run behaves like CI, which never has these untracked files present.
if [ -n "$bad_files" ] && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    ignored=$(printf '%s\n' "$bad_files" | git check-ignore --stdin 2>/dev/null || true)
    if [ -n "$ignored" ]; then
        bad_files=$(printf '%s\n' "$bad_files" | grep -vxF "$ignored" || true)
    fi
fi

# Fail if any exist.
if [ -n "$bad_files" ]; then
    echo -n "::error::"
    echo "The following files should not have their executable bit set:" >&2
    echo "$bad_files" >&2
    exit 1
fi
