#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage_string="
Usage: get-bitstream-strategy.sh <cached-bitstream-design> <bitstream-target-to-check> [pathspec]...

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

bitstream_design=$1
bitstream_check_target=$2

if [ $# -gt 1 ]; then
  excluded_files=( "${@:3}" )
else
  excluded_files=( "." )
fi

# Retrieve the most recent bitstream at or before HEAD.
BITSTREAM="--refresh HEAD" ci/bazelisk.sh build @bitstreams//:manifest

# Find the bitstream commit from the manifest file.
manifest_file=$(ci/scripts/target-location.sh @bitstreams//:manifest)

bitstream_commit=$(ci/bazelisk.sh run //util/py/scripts:get_bitstream_build_id \
  -- --manifest ${manifest_file} \
  --schema ${REPO_TOP}/rules/scripts/bitstreams_manifest.schema.json \
  --design ${bitstream_design})

bazel_to_path() {
  # Loop over bazel label dependencies and turn them into paths
  for dep in $1; do
    # Ignore everything that does not start with "//"
    if [[ ! $dep =~ ^// ]]; then
      continue
    fi
    # Replace the : with a / and remove the leading // to get a file name
    dep=${dep:2}
    dep=${dep//://}
    echo $dep
  done
}

compute_changed_dep() {
  for change in $1; do
    for dep in $2; do
      if [[ $change == "$dep" ]]; then
        echo $change
      fi
    done
  done
}

if [ -z "${bitstream_commit}" ]; then
  echo "Design ${bitstream_design} not found in the cache"
  bitstream_strategy=build
else
  # Use bazel to get a list of dependencies for the bitstream target.
  bazel_labels=$(./bazelisk.sh query "deps(${bitstream_check_target}) + buildfiles(deps(${bitstream_check_target}))")
  dependencies=$(bazel_to_path "${bazel_labels}")

  echo "Checking for changes against pre-built bitstream from ${bitstream_commit}"
  echo "Files changed:"
  git diff --stat --name-only ${bitstream_commit}
  echo

  changed_files=$(git diff --stat --name-only ${bitstream_commit} -- "${excluded_files[@]}")
  echo "Changed files after exclusions applied:"
  echo "${changed_files}"
  echo

  # Filter out files not in the dependency list.
  changed_deps=$(compute_changed_dep "${changed_files}" "${dependencies}")
  echo "Changed dependencies after exclusions applied:"
  echo "${changed_deps}"
  echo

  # Use the cached bitstream if no changed dependencies remain.
  if [ -z "${changed_deps}" ]; then
    bitstream_strategy=cached
  else
    bitstream_strategy=build
  fi
fi

echo "Bitstream strategy is ${bitstream_strategy}"
echo "##vso[task.setvariable variable=bitstreamStrategy]${bitstream_strategy}"
