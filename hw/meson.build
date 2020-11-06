# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Reggen invocation for generating the register headers we use in the software
# to ensure register offsets continue to match the hardware.
gen_hw_hdr_output = '@BASENAME@_regs.h'
gen_hw_hdr_command = [
  prog_python,
  meson.source_root() / 'util/regtool.py',
  '--cdefines',
  '-o', '@OUTPUT@',
  '@INPUT@'
]

# Most IPs are in `hw/ip`
subdir('ip')
# Some IPs are parameterized by `top_earlgrey`, so are in `hw/top_earlgrey/ip`.
# This directory will also contain any topgen-generated libraries.
subdir('top_earlgrey')
