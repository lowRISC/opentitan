#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

echo '' | ./hmac_model.py -v -k DEADBEEF
./hmac_model.py -k DEADBEEF -v message.dat

