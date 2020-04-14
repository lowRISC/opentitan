# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Test status libary.
sw_lib_testing_test_status = declare_dependency(
  link_with: static_library(
    'test_status_ot',
    sources: ['test_status.c'],
    dependencies: [
      sw_lib_mmio,
      sw_lib_base_log,
      sw_lib_runtime_hart,
    ],
  )
)

sw_lib_testing_mock_mmio = declare_dependency(
  link_with: static_library(
    'mock_mmio',
    sources: [
      meson.source_root() / 'sw/device/lib/base/mmio.c',
      meson.source_root() / 'sw/device/lib/base/bitfield.c',
      'mock_mmio.cc',
    ],
    dependencies: [sw_vendor_gtest],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  )
)

# Example test using mock_mmio.h, which also serves to
# test that mock_mmio.h works correctly.
test('mock_mmio_test', executable(
  'mock_mmio_test',
  sources: ['mock_mmio_test.cc'],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  cpp_args: ['-DMOCK_MMIO'],
))
