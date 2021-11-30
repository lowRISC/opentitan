#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script will be run by bazel when the build process wants to generate
# information about the status of the workspace.
#
# The output will be key-value pairs in the form:
# KEY1 VALUE1
# KEY2 VALUE2
#
# If this script exits with a non-zero exit code, it's considered as a failure
# and the output will be discarded.

git_rev=$(git rev-parse HEAD)
if [[ $? != 0 ]];
then
  exit 1
fi
echo "BUILD_SCM_REVISION ${git_rev}"

git_version=$(git describe --always)
if [[ $? != 0 ]];
then
  exit 1
fi
echo "BUILD_GIT_VERSION ${git_version}"

git diff-index --quiet HEAD --
if [[ $? == 0 ]];
then
  tree_status="clean"
else
  tree_status="modified"
fi
echo "BUILD_SCM_STATUS ${tree_status}"
