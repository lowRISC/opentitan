#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

RUSTFMT=@@RUSTFMT@@
RUSTFMT_ARGS=@@RUSTFMT_ARGS@@
WORKSPACE="@@WORKSPACE@@"
rustfmt=$(realpath "$RUSTFMT")

if [[ -n "${WORKSPACE}" ]]; then
    REPO="$(dirname "$(realpath ${WORKSPACE})")"
    cd "${REPO}" || exit 1
elif [[ -n "${BUILD_WORKSPACE_DIRECTORY+is_set}" ]]; then
    cd "${BUILD_WORKSPACE_DIRECTORY}" || exit 1
else
    echo "Neither WORKSPACE nor BUILD_WORKSPACE_DIRECTORY were set."
    echo "If this is a test rule, add 'workspace = \"//:WORKSPACE.bzlmod\"' to your rule."
    exit 1
fi

if [[ $# != 0 ]]; then
    FILES="$*"
else
    FILES=$(find . \
        -type f \
        @@EXCLUDE_PATTERNS@@ \
        \( @@INCLUDE_PATTERNS@@ \) \
        -print)
fi

echo "$FILES" | xargs "$rustfmt" "${RUSTFMT_ARGS[@]}"
