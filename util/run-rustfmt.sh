#!/bin/sh
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

find sw hw \
    -name '*.rs' \
    -exec rustfmt --check {} \;

