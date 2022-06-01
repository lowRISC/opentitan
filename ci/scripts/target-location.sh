#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Use Bazel to query for the location of targets instead of searching

set -e
REPO=$(dirname "$0")/../..

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

exec $REPO/bazelisk.sh cquery $@ --output starlark --starlark:file=$REPO/rules/output.cquery 2>$REDIR
