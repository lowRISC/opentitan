#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Use Bazel to query for the location of targets instead of searching

set -e
readonly REPO_TOP=$(git rev-parse --show-toplevel)

verbose='false'
print_usage() {
  printf "Usage: $0 [-v] <bazel target label>"
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

readonly REL_PATH=$(${REPO_TOP}/bazelisk.sh outquery "$@" 2>$REDIR)
echo "${REPO_TOP}/${REL_PATH}"
