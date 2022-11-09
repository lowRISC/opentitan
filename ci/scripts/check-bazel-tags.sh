#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# The list of bazel tags is represented as a string and checked with a regex
# https://bazel.build/query/language#attr
# This function takes a tag(or regex component) and wraps it so attr can query
# for exact matches.
exact_regex () {
  echo "[\\[ ]${1}[,\\]]"
}

check_empty () {
    if [[ ${1} ]]; then
        echo "Error:"
        echo "$1"|sed 's/^/    /';
        echo "$2"
        exit 1
    fi
}

# This check ensures OpenTitan software can be built with a wildcard without
# waiting for Verilator using --build_tag_filters=-verilator
untagged=$(./bazelisk.sh query \
  "rdeps(
      //...,
      //hw:verilator
  )
  except
  attr(
      tags,
      '$(exact_regex "(verilator|manual)")',
      //...
  )" \
  --output=label_kind)
check_empty "${untagged}" \
"Target(s) above depend(s) on //hw:verilator; please tag it with verilator or
(to prevent matching any wildcards) manual.
NOTE: test_suites that contain bazel tests with different tags should almost
universally use the manual tag."

# This check ensures OpenTitan software can be built with wildcards in
# environments that don't have vivado or vivado tools installed by using
# --build_tag_filters=-vivado.
untagged=$(./bazelisk.sh query \
  "rdeps(
      //...,
      kind(
          'bitstream_splice',
          //...
      )
  )
  except
  attr(
      tags,
      '$(exact_regex "(cw310_rom|cw310_test_rom|vivado|manual)")',
      //...
  )" \
  --output=label_kind)
check_empty "${untagged}" \
"Target(s) above depend(s) on a bitstream_splice that isn't cached.
Please tag it with vivado or (to prevent matching any wildcards) manual.
NOTE: test_suites that contain tests with different sets of tags should almost
universally use the manual tag."
