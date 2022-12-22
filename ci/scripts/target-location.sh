#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Use Bazel to query for the location of targets instead of searching

set -e
REPO_TOP=$(git rev-parse --show-toplevel)
readonly REPO_TOP

verbose='false'
print_usage() {
  printf "Usage: $0 [-v] <bazel target label> [bazel options...]"
}

while getopts 'v' flag; do
  case "${flag}" in
    v) verbose='true' ;;
    *) print_usage
       exit 1 ;;
  esac
done

shift $((OPTIND-1))

REDIR='/dev/stderr'
if [ $verbose == 'false' ];
then
  REDIR='/dev/null'
fi

REL_PATH=$(${REPO_TOP}/bazelisk.sh outquery "$@" 2>$REDIR)
readonly REL_PATH
REPO_EXECROOT=$(${REPO_TOP}/bazelisk.sh info --show_make_env execution_root)
readonly REPO_EXECROOT
echo "${REPO_EXECROOT}/${REL_PATH}"
