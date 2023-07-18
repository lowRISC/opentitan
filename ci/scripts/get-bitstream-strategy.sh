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

bitstream_strategy=build

echo
echo "Bitstream strategy is ${bitstream_strategy}"
echo "##vso[task.setvariable variable=bitstreamStrategy]${bitstream_strategy}"
