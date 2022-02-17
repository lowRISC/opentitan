# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_silicon_creator_lib_base_mock_csr = declare_dependency(
  link_with: static_library(
    'mock_csr',
    sources: [
      'mock_csr.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
    c_args: ['-DMOCK_CSR'],
    cpp_args: ['-DMOCK_CSR'],
  )
)

# Example test using mock_csr.h, which also serves to
# test that mock_csr.h works correctly.
test('mock_csr_test', executable(
  'mock_csr_test',
  sources: ['mock_csr_test.cc'],
  dependencies: [
    sw_vendor_gtest,
    sw_silicon_creator_lib_base_mock_csr,
  ],
  native: true,
  cpp_args: ['-DMOCK_CSR'],
))

# Mask ROM Secure MMIO module
sw_silicon_creator_lib_base_sec_mmio = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_base_sec_mmio',
    sources: [
      'sec_mmio.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
    ],
  ),
)

sw_silicon_creator_lib_base_mock_sec_mmio = declare_dependency(
  link_with: static_library(
    'mock_sec_mmio',
    sources: [
      'mock_sec_mmio.h',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
    ],
    native: true,
  )
)

test('sw_silicon_creator_lib_base_sec_mmio_unittest', executable(
    'sw_silicon_creator_lib_base_sec_mmio_unittest',
    sources: [
      'sec_mmio_unittest.cc',
      'sec_mmio.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_hardened,
      sw_lib_testing_mock_abs_mmio,
    ],
    native: true,
    c_args: [
      '-DMOCK_ABS_MMIO',
      '-DOT_OFF_TARGET_TEST',
    ],
    cpp_args: [
      '-DMOCK_ABS_MMIO',
      '-DOT_OFF_TARGET_TEST',
    ],
  ),
  suite: 'mask_rom',
)
