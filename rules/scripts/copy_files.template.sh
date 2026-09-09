#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# --- begin runfiles.bash initialization v3 ---
# Copy-pasted from the Bazel Bash runfiles library at:
# https://github.com/bazelbuild/bazel/blob/master/tools/bash/runfiles/runfiles.bash
set -uo pipefail
set +e
f=bazel_tools/tools/bash/runfiles/runfiles.bash
# shellcheck source=/dev/null
source "${RUNFILES_DIR:-/dev/null}/$f" 2>/dev/null || \
  source "$(grep -sm1 "^$f " "${RUNFILES_MANIFEST_FILE:-/dev/null}" | cut -f2- -d' ')" 2>/dev/null || \
  source "$0.runfiles/$f" 2>/dev/null || \
  source "$(grep -sm1 "^$f " "$0.runfiles_manifest" | cut -f2- -d' ')" 2>/dev/null || \
  source "$(grep -sm1 "^$f " "$0.exe.runfiles_manifest" | cut -f2- -d' ')" 2>/dev/null || \
  {
    echo >&2 "ERROR: cannot find @bazel_tools//tools/bash/runfiles:runfiles.bash"
    exit 1
  }
f=
set -e
# --- end runfiles.bash initialization v3 ---

DEST_RLOCATION="__DEST_RLOCATION__"
FILES=(__FILES__)

ANCHOR_PATH="$(rlocation "$DEST_RLOCATION")"
if [[ -z "$ANCHOR_PATH" || ! -e "$ANCHOR_PATH" ]]; then
    echo "Error: Could not locate destination anchor in runfiles: $DEST_RLOCATION"
    exit 1
fi

# Follow symlinks to find the physical source directory on disk.
DEST_DIR="$(dirname "$(realpath "$ANCHOR_PATH")")"
if [[ ! -d "$DEST_DIR" ]]; then
    echo "Error: Resolved destination '$DEST_DIR' is not a directory."
    exit 1
fi

# Copy the files from runfiles to the destination.
for f in "${FILES[@]}"; do
  SRC="$(rlocation "$f")"
  if [[ -z "$SRC" || ! -e "$SRC" ]]; then
    echo "Error: Could not locate source file in runfiles: $f"
    exit 1
  fi
  cp --no-preserve=mode "$SRC" "$DEST_DIR"
done
