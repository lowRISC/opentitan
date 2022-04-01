#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Helper script that cleans up the input from stdin (presumed to be the output
# of e.g. clang -E) which removes extraneous metadata, such as line-number
# directives, which is not particularly useful for readers; also, hits the output
# with clang-format (if available as the $CLANG_FORMAT variable).

set -e

# The first regular expression removes any line starting with `# 123`, which
# the preprocessor inserts as a sort of "context string" (this is a GCC-specific
# extension that Clang also implements). We then shove it into clang-format.
perl -pe 's/# \d+.+$//g' \
    | perl -0777pe 's/\n{2,}/\n\n/g' \
    | "${CLANG_FORMAT:-cat}"
