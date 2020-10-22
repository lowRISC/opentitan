# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('freestanding')

# Non volatile bit manipulation helper library (sw_lib_bitfield).
sw_lib_bitfield = declare_dependency(
  link_with: static_library(
    'bitfield_ot',
    sources: ['bitfield.c'],
  )
)

# Memory Operations library (sw_lib_mem)
sw_lib_mem = declare_dependency(
  link_with: static_library(
    'mem_ot',
    sources: ['memory.c'],
    c_args: ['-fno-builtin'],
  )
)

# MMIO register manipulation library
sw_lib_mmio = declare_dependency(
  link_with: static_library(
    'mmio_ot',
    sources: ['mmio.c'],
    dependencies: [
      sw_lib_bitfield,
      sw_lib_mem,
    ],
  )
)
