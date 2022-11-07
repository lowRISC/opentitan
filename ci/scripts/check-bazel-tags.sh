#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# The list of bazel tags is represented as a string and checked with a regex
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
# waiting for Verilator using --build_tag_filters=-verilator, it also enables
# verilator tests to be filtered out.
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
"Target(s) above depend(s) on //hw:verilator, please tag it with verilator or manual."

# This check ensures Opentitan software can be built with wildcards in
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
"Target(s) above depend(s) on a bitstream_splice and isn't available in a cache.
Please tag it with vivado or manual."

# This check ensures cw310 users may group tests that depend on the cached
# cw310_test_rom bitstream.
mistagged=$(./bazelisk.sh query \
    "tests(
        rdeps(
            attr(
                tags,
                '$(exact_regex cw310_test_rom)',
                tests(//...)
            ),
            kind(
                'bitstream_splice',
                //...
            )
            except
            deps(
                //hw/bitstream:test_rom
            )
        )
    )" \
    --output=label_kind)
check_empty "${mistagged}" \
"Target(s) above depend(s) on a bitstream_splice other than those used to generate the test_rom.
Please tag as cw310_*_variant if you intended to use another bitstream."

# This check ensures cw310 users may group tests that depend on the cached
# cw310_rom bitstream.
mistagged=$(./bazelisk.sh query \
    "tests(
        rdeps(
            attr(
                tags,
                '$(exact_regex cw310_rom)',
                //...
            ),
            kind(
                'bitstream_splice',
                //...
            )
            except
            deps(//hw/bitstream:rom)
        )
    )" \
    --output=label_kind)
check_empty "${mistagged}" \
"Above target(s) depend(s) on a bitstream_splice other than those used to generate the rom.
Please tag as cw310_*_variant if you intend to use another bitstream."
