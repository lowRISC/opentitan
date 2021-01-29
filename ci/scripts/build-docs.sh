#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Build docs and tell the Azure runner to upload any doxygen warnings

set -e
util/build_docs.py || {
  echo -n "##vso[task.logissue type=error]"
  echo "Documentation build failed."
  exit 1
}

# Upload Doxygen Warnings if Present
if [ -f "build/docs-generated/sw/doxygen_warnings.log" ]; then
  echo -n "##vso[task.uploadfile]"
  echo "${PWD}/build/docs-generated/sw/doxygen_warnings.log"
  # Doxygen currently generates lots of warnings.
  # echo -n "##vso[task.issue type=warning]"
  # echo "Doxygen generated warnings. Use 'util/build_docs.py' to generate warning logfile."
fi
