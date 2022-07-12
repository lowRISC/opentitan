#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# cd into $REPO_TOP
cd "$(dirname "$(readlink -e "${BASH_SOURCE[0]}")")"/../..

EXCLUDED_DIRS="-name third_party -o -name vendor -o -name lowrisc_misc-linters"
# Get an array of all shell scripts to check using input redirection and
# process substitution. For details on this syntax, see ShellCheck SC2046.
readarray -t shell_scripts < \
    <(find . \( $EXCLUDED_DIRS \) -prune -o -name '*.sh' -print)
shellcheck --severity=warning "${shell_scripts[@]}"
