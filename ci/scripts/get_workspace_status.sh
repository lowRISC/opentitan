#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script is passed to bazel's `--workspace_status_command` to generate
# the workspace status. To ensure reproducible builds, we output constant
# values.

echo "BUILD_GIT_VERSION OpenTitanCI"
echo "BUILD_SCM_REVISION 123456789"
echo "BUILD_SCM_STATUS modified"
echo "BUILD_TIMESTAMP 315532800"
