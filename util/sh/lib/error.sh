# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash

error() {
    log "ERROR: $1" 1 >&2
    exit 1
}
