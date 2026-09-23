#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

function run() {
    echo "$@"
    "$@"
}

export HSMTOOL_TOKEN=fake_keys
export HSMTOOL_USER=user
export HSMTOOL_PIN=123456

# SoftHSM2 doesn't like the symlinks bazel sets up.
# Make a copy of the token and operate on the copy.
if [[ -n "${SOFTHSM2_CONF:+x}" ]]; then
    DIR=$(dirname ${SOFTHSM2_CONF})
    cp -aL $DIR/tokens $DIR/token
    sed -e "s/tokens/token/g" $SOFTHSM2_CONF >softhsm2.conf
    export SOFTHSM2_CONF=softhsm2.conf
fi
