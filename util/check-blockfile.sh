#!/bin/sh
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

echo "Checking BLOCKFILE. This will output all files blocked from changes and "
echo "a warning if there are any patterns in BLOCKFILES which don't match any "
echo "file. Must be run from repository root."

# Produce a list of all files, chop off the first two characters which as './'
# as the change blocker script doesn't work correctly with them.
find -type f | cut -c 3- > ot-filelist

./ci/scripts/check-pr-changes-allowed.py \
  --plain-block-msg \
  --report-unused-patterns \
  ot-filelist
