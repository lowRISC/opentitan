#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CLANG_FORMAT=@@CLANG_FORMAT@@
MODE=@@MODE@@

clang_format=$(readlink "$CLANG_FORMAT")

if ! cd "$BUILD_WORKSPACE_DIRECTORY"; then
    echo "Unable to change to workspace (BUILD_WORKSPACE_DIRECTORY: ${BUILD_WORKSPACE_DIRECTORY})"
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
        exit 2
esac
