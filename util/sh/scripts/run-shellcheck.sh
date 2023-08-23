#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Escape the sandbox when running under `bazel test`. This script assumes that
# when it's invoked by Bazel, the Bazel target will depend on `//:WORKSPACE`.
# This assumption enables us to infer that we're running in the sandbox when we
# see a symlink named "WORKSPACE".
if [[ -L WORKSPACE ]]; then
    SHELLCHECK="$(realpath external/shellcheck/shellcheck)"
    REPO_TOP="$(dirname "$(realpath WORKSPACE)")"
    cd "${REPO_TOP}"
else
    REPO_TOP="$(git rev-parse --show-toplevel)"
    cd "${REPO_TOP}"
    SHELLCHECK="./bazelisk.sh run @shellcheck//:shellcheck --"
fi

EXCLUDED_DIRS="-name third_party -o -name vendor -o -name lowrisc_misc-linters"
# Get an array of all shell scripts to check using input redirection and
# process substitution. For details on this syntax, see ShellCheck SC2046.
# shellcheck disable=SC2046
readarray -t shell_scripts < \
    <(find . \( $EXCLUDED_DIRS \) -prune -o -name '*.sh' -print)

$SHELLCHECK --severity=warning "${shell_scripts[@]}"
