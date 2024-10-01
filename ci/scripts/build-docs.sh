#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Build docs and tell the Azure runner to upload any doxygen warnings

set -e
util/site/build-docs.sh build-local || {
  echo "::error::Documentation build failed."
  exit 1
}
