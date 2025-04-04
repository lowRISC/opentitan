#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

DEST="__DEST__"
FILES=(__FILES__)

# Change directory into the root of the project.
if [[ ! -z "${BUILD_WORKSPACE_DIRECTORY+is_set}" ]]; then
    cd ${BUILD_WORKSPACE_DIRECTORY} || exit 1
else
    echo "BUILD_WORKSPACE_DIRECTORY was not set."
    echo "This rule should be executable and invoked with 'bazel run'."
    exit 1
fi

# Since we may be building resources in an externally attached workspace,
# determine the real path to that workspace.
if [[ -z "${__WORKSPACE__+is_set}" ]]; then
    echo "__WORKSPACE__ was not set."
    exit 1
fi

WORKSPACE="$(realpath "${__WORKSPACE__}")"
if [[ ! -d "$WORKSPACE" ]]; then
    echo "$WORKSPACE isn't a directory."
    exit 1
fi

# Copy the files from the source (e.g. bazel-out) to the destination.
for f in "${FILES[@]}"; do
  cp --no-preserve=mode "$f" "$WORKSPACE/$DEST"
done
