#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

DEST="__DEST__"
FILES=(__FILES__)

if [[ ! -z "${__WORKSPACE__+is_set}" ]]; then
    cd ${__WORKSPACE__} || exit 1
else
    echo "__WORKSPACE__ was not set."
    exit 1
fi

for f in "${FILES[@]}"; do
  cp --no-preserve=mode "$f" "$DEST"
done
