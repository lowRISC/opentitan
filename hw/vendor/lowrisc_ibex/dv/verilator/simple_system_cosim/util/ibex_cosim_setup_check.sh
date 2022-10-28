#!/bin/sh

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SPIKE_PCS="riscv-riscv riscv-disasm riscv-fdt"

if ! (pkg-config --exists "$SPIKE_PCS")
then
  echo "Failed to find Spike pkg-config packages. Did you add lib/pkgconfig"\
       "from your spike install to PKG_CONFIG_PATH?"
  exit 1
fi
