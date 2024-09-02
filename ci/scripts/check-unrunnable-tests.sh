#!/bin/bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Look for all tests are incompatible with host, i.e. unrunnable.
# The cquery will output an empty string for compatible tests and
# a non-empty string (test name) for the incompatible ones. Therefore
# we filter out the empty lines.
ci/bazelisk.sh cquery 'tests(//...)' \
    --noinclude_aspects \
    --define DISABLE_VERILATOR_BUILD=true \
    --output=starlark \
    --starlark:file=ci/scripts/incompatible_targets.cquery \
    | sed '/^$/d' > output.txt
if [ -s output.txt ]; then
    echo "The following tests are incompatible with the host platform:"
    cat output.txt
    exit 1
fi
