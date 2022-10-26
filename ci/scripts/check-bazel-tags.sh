#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

untagged=$(./bazelisk.sh query "rdeps(//..., //hw:verilator) except attr(tags, '[\\[ ](verilator|manual)[,\\]]', //...)")
if [[ ${untagged} ]]; then # Check that all targets that depend on verilator are tagged
  echo "Target(s): ${untagged} depend(s) on //hw:verilator, please tag it with verilator or manual";
  exit 1
fi

untagged=$(./bazelisk.sh query "rdeps(//..., kind('bitstream_splice', //...)) except attr(tags, '[\\[ ](cw310_rom|cw310_test_rom|vivado|manual)[,\\]]', //...)")
if [[ ${untagged} ]]; then # Check that all targets that depend on vivado are tagged
  echo "Target(s): ${untagged} depend(s) on a bitstream_splice but isn't tagged with vivado or manual";
  exit 1
fi
