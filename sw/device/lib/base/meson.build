# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('freestanding')
subdir('testing')

sw_lib_math_builtins = declare_dependency(
  link_with: static_library(
    'math_builtins_ot',
    sources: ['math_builtins.c'],
    c_args: ['-fno-builtin'],
  )
)

sw_lib_math = declare_dependency(
  link_with: static_library(
    'math_ot',
    sources: ['math.c', 'math_builtins.c'],
  ),
  dependencies: [sw_lib_math_builtins],
)

# Non volatile bit manipulation helper library (sw_lib_bitfield).
sw_lib_bitfield = declare_dependency(
  link_with: static_library(
    'bitfield_ot',
    sources: ['bitfield.c'],
  ),
  dependencies: [sw_lib_math],
)

sw_lib_abs_mmio = declare_dependency(
  link_with: static_library(
    'sw_lib_abs_mmio',
    sources: [
      'abs_mmio.c',
    ],
  ),
  dependencies: [sw_lib_math],
)


# Memory Operations library (sw_lib_mem)
sw_lib_mem = declare_dependency(
  link_with: static_library(
    'mem_ot',
    sources: ['memory.c'],
    c_args: ['-fno-builtin'],
  ),
  dependencies: [sw_lib_math],
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

sw_lib_random_order = declare_dependency(
  link_with: static_library(
    'random_order_ot',
    sources: ['random_order.c'],
    dependencies: [sw_lib_bitfield],
  )
)
