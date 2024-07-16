#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CLANG_FORMAT=@@CLANG_FORMAT@@
MODE=@@MODE@@
WORKSPACE="@@WORKSPACE@@"
clang_format=$(realpath "$CLANG_FORMAT")

if [[ ! -z "${WORKSPACE}" ]]; then
    REPO="$(dirname "$(realpath ${WORKSPACE})")"
    cd ${REPO} || exit 1
elif [[ ! -z "${BUILD_WORKSPACE_DIRECTORY+is_set}" ]]; then
    cd ${BUILD_WORKSPACE_DIRECTORY} || exit 1
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

case "$MODE" in
    diff)
        RESULT=0
        for f in $FILES; do
            diff -Naur "$f" <(${clang_format} ${f})
            RESULT=$(($RESULT | $?))
        done
        exit $RESULT
        ;;
    fix)
        echo "$FILES" | xargs ${clang_format} -i
        ;;
    *)
        echo "Unknown mode: $MODE"
        exit 1
esac
