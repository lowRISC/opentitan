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
"Target(s) above depend(s) on //hw:verilator, please tag it with verilator or
(to prevent matching any wildcards) manual.
NOTE: test_suites that contain targets with different tags should almost
universally use the manual tag."

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
"Target(s) above depend(s) on a bitstream_splice that isn't cached.
Please tag it with vivado or (to prevent matching any wildcards) manual.
NOTE: test_suites that contain targets with different tags should almost
universally use the manual tag."

# This check ensures cw310 users may group tests that depend on the cached
# cw310_test_rom bitstream.
mistagged=$(./bazelisk.sh query \
    "tests(`# Only output tests`
        rdeps(
            attr(`# Anything tagged cw310_test_rom`
                tags,
                '$(exact_regex cw310_test_rom)',
                tests(//...)
            ),
            kind(`# That depends on a bitstream splice`
                'bitstream_splice',
                //...
            )
            except`# Other than those used to build the test_ROM bitstream`
            deps(
                //hw/bitstream:test_rom
            )
        )
    )" \
    --output=label_kind)
check_empty "${mistagged}" \
"Target(s) above depend(s) on a bitstream_splice rule other than those used to
generate the cached bitstream with the test_ROM, but is tagged with cw310_test_rom.
Please either:
-Correct the dependencies to exclude other bitstream_splices,
-Correct the target by setting it to something other than cw310_test_rom,
-Remove the cw310_test_rom tag.
NOTE: test_suites that contain targets with different tags should almost
universally use the manual tag."



# This check ensures cw310 users may group tests that depend on the cached
# cw310_rom bitstream.
mistagged=$(./bazelisk.sh query \
    "tests(`# Only output tests`
        rdeps(
            attr(`# Anything tagged cw310_rom`
                tags,
                '$(exact_regex cw310_rom)',
                //...
            ),
            kind(`# That depends on a bitstream splice`
                'bitstream_splice',
                //...
            )
            except`# Other than those used to build the ROM bitstream`
            deps(//hw/bitstream:rom)
        )
    )" \
    --output=label_kind)
check_empty "${mistagged}" \
"Target(s) above depend(s) on a bitstream_splice rule other than those used to
generate the cached bitstream with the ROM, but is tagged with cw310_rom.
Please either:
-Correct the dependencies to exclude other bitstream_splices,
-Correct the target by setting it to something like cw310_rom_variant,
-Correct the tag by setting it to cw310_rom_variant.
NOTE: test_suites that contain targets with different tags should almost
universally use the manual tag."
