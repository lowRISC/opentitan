#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper that duplicates the code for the quick lint job in
# azure-pipelines.yml. The two should be kept in sync.
#
# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request.

set -e

echo -e "\n### Use buiildifier to check Bazel coding style"
bazel run buildifier_check

echo "### Check vendored directories are up-to-date"
ci/scripts/check-vendoring.sh
