#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

DEST="__DEST__"
FILES=(__FILES__)

if [[ ! -z "${RUNFILES_DIR+is_set}" ]]; then
    true
elif [[ -d "$0.runfiles" ]]; then
    RUNFILES_DIR="$0.runfiles"
else
    echo "Could not find runfiles directory."
    exit 1
fi

RUNFILES_DIR="$(realpath "$RUNFILES_DIR")"

RELATIVE_TO_RUNFILE="__RELATIVE_TO_RUNFILE__"
RELATIVE_TO_PATH="$RUNFILES_DIR/$RELATIVE_TO_RUNFILE"

if [[ ! -f "$RELATIVE_TO_PATH" ]]; then
    echo "Could not find relative_to file in runfiles: $RELATIVE_TO_PATH"
    exit 1
fi

RESOLVED_PATH="$(realpath "$RELATIVE_TO_PATH")"
DEST_DIR="$(dirname "$RESOLVED_PATH")"

if [[ ! -d "$DEST_DIR" ]]; then
    echo "Destination directory does not exist: $DEST_DIR"
    exit 1
fi

# Change directory into the root of the project.
if [[ ! -z "${BUILD_WORKSPACE_DIRECTORY+is_set}" ]]; then
    cd ${BUILD_WORKSPACE_DIRECTORY} || exit 1
else
    echo "BUILD_WORKSPACE_DIRECTORY was not set."
    echo "This rule should be executable and invoked with 'bazel run'."
    exit 1
fi

# Copy the files from the source (e.g. bazel-out) to the destination.
for f in "${FILES[@]}"; do
  cp --no-preserve=mode "$f" "$DEST_DIR"
done
