#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Run the auto-instrumentation tool on all sources of the
# `asm_library_with_coverage` macro.

set -eo pipefail

mapfile -t files < <(
    ci/bazelisk.sh query '
        kind("source file",
            deps(labels(srcs,
                kind(asm_source_with_coverage, //sw/...)
            ))
        )' --output=location \
    | cut -d ':' -f 1
)

if [[ "${#files[@]}" -ne 0 ]]; then
    echo "Found ${#files[@]} instrumented asm source files"
    for path in "${files[@]}"; do
        echo "${path}"
    done
    ci/bazelisk.sh run //util/coverage/asm:instrument -- \
        --files "${files[@]}" "$@"
else
    echo "No instrumented asm source file"
fi
