# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash

function log() {
    local msg="$1"
    local stack_offset=${2:-0}
    local timestamp
    timestamp=$(date +"%Y-%m-%dT%H:%M:%S%z")
    local file=${BASH_SOURCE[$((stack_offset + 1))]##*/}
    local line=${BASH_LINENO[${stack_offset}]}
    echo "${timestamp} ${file}:${line}: ${msg}"
}
