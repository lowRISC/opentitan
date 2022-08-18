#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage_string="
Usage: get-bitstream-strategy.sh <cached-bitstream-target> [pathspec]...

    cached-bitsream-target The bazel target for the cached bitstream. This script
                           will retrieve the most recent image from a commit in this
                           this branch's history.
    pathspec A git pathspec (multiple instances permitted) indicating which files
                   trigger building the bitstream. Please use only exclude pathspecs
                   to cause new, unconsidered paths to trigger the build.
"

if [ $# -lt 1 ]; then
  echo >&2 "ERROR: Unexpected number of arguments"
  echo >&2 "${usage_string}"
  exit 1
fi

. util/build_consts.sh

bitstream_target=${*:1:1}

if [ $# -gt 1 ]; then
  excluded_files=( "${@:2}" )
else
  excluded_files=( "." )
fi

# Retrieve the most recent bitstream at or before HEAD.
BITSTREAM="--refresh HEAD" ./bazelisk.sh build ${bitstream_target}

# The directory containing the bitstream is named after the git hash.
bitstream_file=$(ci/scripts/target-location.sh ${bitstream_target})
bitstream_commit=$(basename "$(dirname ${bitstream_file})")

echo "Checking for changes against pre-built bitstream from ${bitstream_commit}"
echo "Files changed:"
git diff --stat --name-only ${bitstream_commit}
echo
echo "Changed files after exclusions applied:"
# Use the cached bitstream if no changed files remain.
if git diff --exit-code --stat --name-only ${bitstream_commit} -- "${excluded_files[@]}"; then
  bitstream_strategy=cached
else
  bitstream_strategy=build
fi

echo
echo "Bitstream strategy is ${bitstream_strategy}"
echo "##vso[task.setvariable variable=bitstreamStrategy]${bitstream_strategy}"
