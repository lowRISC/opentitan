# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('freestanding')
subdir('testing')

# Non volatile bit manipulation helper library (sw_lib_bitfield).
sw_lib_bitfield = declare_dependency(
  link_with: static_library(
    'bitfield_ot',
    sources: ['bitfield.c'],
  )
)

sw_lib_abs_mmio = declare_dependency(
  link_with: static_library(
    'sw_lib_abs_mmio',
    sources: [
      'abs_mmio.c',
    ],
    dependencies: [],
  ),
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

sw_lib_hardened = declare_dependency(
  link_with: static_library(
    'hardened_ot',
    sources: [
      'hardened.c'
    ],
  )
)

test('base_hardened_unittest', executable(
    'base_hardened_unittest',
    sources: [
      'hardened.c',
      'hardened_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'base',
)
