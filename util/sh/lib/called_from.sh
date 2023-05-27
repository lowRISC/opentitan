# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash

source util/sh/lib/log.sh

called_from() {
    local file=${BASH_SOURCE[2]##*/}
    local line=${BASH_LINENO[1]}
    log "Called from: ${file}:${line}" 1
}
