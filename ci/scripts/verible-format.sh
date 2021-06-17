#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around Verible format, used for CI.

set -e

util/verible-format.py --allowlist || {
  echo -n "##vso[task.logissue type=error]"
  echo "Verilog format with Verible failed. Run 'util/verible-format.py' to check and fix all errors."
  echo "This flow is currently experimental and failures can be ignored."
  exit 1
}
