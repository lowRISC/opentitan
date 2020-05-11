#!/bin/sh
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

find sw hw \
    \( -name '*.cpp' \
    -o -name '*.cc' \
    -o -name '*.c' \
    -o -name '*.h' \) \
    -exec clang-format -i {} \;

# Report on missing curly braces for loops and control statements.
# clang-format cannot fix them for us, so this requires manual work.
#
# This does not cope with `do { ... } while (cond)` as used in macros (without
# the semicolon).
#
# This rule does not use the `.clang-format` file so vendor must be excluded.
braces_missing=$(
    find sw hw \
        -not \( -path '*/vendor/*' -prune \) \
        \( -name '*.cpp' \
        -o -name '*.cc' \
        -o -name '*.c' \
        -o -name '*.h' \) \
       -exec grep -Hn -P '(^|\s)((if|while|for) \(.+\)|else\s*)$' {} \;
)
if [ ! -z "$braces_missing" ]; then
    echo ERROR: Curly braces are missing from the following control or loop
    echo statements. Please add them manually and re-run this script.
    echo
    echo "$braces_missing"
    exit 1
fi
