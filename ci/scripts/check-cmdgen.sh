#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks the documentation's CMDGEN blocks are up to date
# (Look at the docstring for 'util/cmdgen.py' to understand how this tool works.)

set -e

./util/cmdgen.py '**/*.md' || {
  echo -n "##vso[task.logissue type=error]"
  echo "Documentation generated using CMDGEN blocks is not up to date."
  echo "Update blocks with: ./util/cmdgen.py -u '**/*.md'"
  exit 1
}
