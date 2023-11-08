#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage_string="
Usage: get-bitstream-strategy.sh <cached-bitstream-design> [pathspec]...

    cached-bitstream-design The design name for the cached bitstream. This script
                            will retrieve the most recent image from a commit in
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

bitstream_design=${*:1:1}

if [ $# -gt 1 ]; then
  excluded_files=( "${@:2}" )
else
  excluded_files=( "." )
fi

# Retrieve the most recent bitstream at or before HEAD.
BITSTREAM="--refresh HEAD" ./bazelisk.sh build @bitstreams//:manifest

# Find the bitstream commit from the manifest file.
manifest_file=$(ci/scripts/target-location.sh @bitstreams//:manifest)

bitstream_commit=$(./bazelisk.sh run //util/py/scripts:get_bitstream_build_id \
  -- --manifest ${manifest_file} \
  --schema ${REPO_TOP}/rules/scripts/bitstreams_manifest.schema.json \
  --design ${bitstream_design})

if [ -z "${bitstream_commit}" ]; then
  echo "Design ${bitstream_design} not found in the cache"
  bitstream_strategy=build
else
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
fi

# Force using cached bitstreams for this test
bitstream_strategy=cached
echo
echo "Bitstream strategy is ${bitstream_strategy}"
echo "##vso[task.setvariable variable=bitstreamStrategy]${bitstream_strategy}"
