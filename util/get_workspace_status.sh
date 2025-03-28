#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
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

# Some of the variables are also exported as "stable variables" to ensure the
# values are always up-to-date when building with --stamp, including:
#
#   * git commit hash - only changes when switching commit.
#   * git working tree status (i.e. clean / modified).
#
# More info about the difference between stable and volatile variables is
# available in https://bazel.build/docs/user-manual#workspace-status-command.

git_rev=$(git rev-parse HEAD)
if [[ $? != 0 ]];
then
  exit 1
fi
echo "BUILD_SCM_REVISION ${git_rev}"
echo "STABLE_BUILD_SCM_REVISION ${git_rev}"

git_rev_short=$(git rev-parse --short=8 HEAD)
if [[ $? != 0 ]];
then
  exit 1
fi
echo "BUILD_SCM_REVISION_SHORT ${git_rev_short}"

git_version=$(git describe --always --tags)
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
echo "STABLE_BUILD_SCM_STATUS ${tree_status}"
