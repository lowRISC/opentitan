#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Escape the sandbox when running under `bazel test`. This script assumes that
# when it's invoked by Bazel, the Bazel target will depend on `//:WORKSPACE.bazel`.
# This assumption enables us to infer that we're running in the sandbox when we
# see a symlink named "WORKSPACE".
if [ -z "${WORKSPACE+x}" ]; then
    REPO_TOP="$(git rev-parse --show-toplevel)"
    SHELLCHECK="./bazelisk.sh run @rules_shellcheck//:shellcheck --"
else
    REPO_TOP="$(dirname "$(realpath "$WORKSPACE")")"
    SHELLCHECK="$(realpath "$SHELLCHECK")"
fi


cd "${REPO_TOP}"

EXCLUDED_DIRS=(-name third_party -o -name vendor -o -name lowrisc_misc-linters)

readarray -t shell_scripts < \
    <(find . '(' "${EXCLUDED_DIRS[@]}" ')' -prune -o -name '*.sh' -print)

"$SHELLCHECK" --severity=warning "${shell_scripts[@]}"
