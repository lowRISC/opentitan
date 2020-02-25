# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('freestanding')

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
  )
)

# Basic printing library (sw_lib_base_print)
sw_lib_base_print = declare_dependency(
  link_with: static_library(
    'base_print_ot',
    sources: ['print.c'],
  )
)

# Generic logging library (sw_lib_base_log)
sw_lib_base_log = declare_dependency(
  link_with: static_library(
    'base_log_ot',
    sources: ['log.c'],
    dependencies: [
      sw_lib_base_print,
    ],
  )
)

test('sw_lib_base_print_test', executable(
  'sw_lib_base_print_test',
  sources: ['print.c', 'print_test.cc'],
  dependencies: [
    sw_vendor_gtest,
  ],
  native: true,
))

