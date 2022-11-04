#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

untagged=$(./bazelisk.sh query "rdeps(//..., //hw:verilator) except attr(tags, '[\\[ ](verilator|manual)[,\\]]', //...)" --output=label_kind)
if [[ ${untagged} ]]; then # Check that all targets that depend on verilator are tagged
  echo "Error:";
  echo "${untagged}"|sed 's/^/    /';
  echo "Target(s) above depend(s) on //hw:verilator, please tag it with verilator or manual.";
  exit 1
fi

untagged=$(./bazelisk.sh query "rdeps(//..., kind('bitstream_splice', //...)) except attr(tags, '[\\[ ](cw310_rom|cw310_test_rom|vivado|manual)[,\\]]', //...)" --output=label_kind)
if [[ ${untagged} ]]; then # Check that all targets that depend on vivado are tagged
  echo "Error:";
  echo "${untagged}"|sed 's/^/    /';
  echo "Target(s) above depend(s) on a bitstream_splice and isn't available in a cache."
  echo "Please tag it with vivado or manual.";
  exit 1
fi

mistagged=$(./bazelisk.sh query "rdeps(attr(tags, '[\\[ ]cw310_test_rom[,\\]]',//...), kind('bitstream_splice', //...) except deps(//hw/bitstream:test_rom))" --output=label_kind)
if [[ ${mistagged} ]]; then # Check that all cw310_test_rom tagged targets don't depend on other bistream_splices
  echo "Error:";
  echo "${mistagged}"|sed 's/^/    /';
  echo "Target(s) above depend(s) on a bitstream_splice other than those used to generate the test_rom.";
  echo "Please tag as cw310_other if you intended to use another bitstream_splice.";
  exit 1
fi

mistagged=$(./bazelisk.sh query "rdeps(attr(tags, '[\\[ ]cw310_rom[,\\]]',//...), kind('bitstream_splice', //...) except deps(//hw/bitstream:rom))" --output=label_kind)
if [[ ${mistagged} ]]; then # Check that all cw310_rom tagged targets don't depend on other bitstream_splices
  echo "Error:";
  echo "${mistagged}"|sed 's/^/    /';
  echo "Above target(s) depend(s) on a bitstream_splice other than those used to generate the rom.";
  echo "Please tag as cw310_other if you intend to use another bitstream_splice.";
  exit 1
fi
