# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash

source util/sh/lib/error.sh
source util/sh/lib/called_from.sh

last_command=""
preexec() {
    last_command="${BASH_COMMAND}"
}

handle_error() {
    local status_code=$?
    if [ $status_code -ne 0 ]; then
        called_from >&2
        error "Command '${last_command}' exited with non-zero status code: ${status_code}"
    fi
}

trap 'preexec' DEBUG
trap 'handle_error' ERR
