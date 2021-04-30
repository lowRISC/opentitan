# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_silicon_creator_lib_base_abs_mmio = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_base_abs_mmio',
    sources: [
      'abs_mmio.c',
    ],
    dependencies: [],
  ),
)

sw_silicon_creator_lib_base_mock_abs_mmio = declare_dependency(
  link_with: static_library(
    'mock_abs_mmio',
    sources: [
      'mock_abs_mmio.h',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  )
)

# Mask ROM Secure MMIO module
sw_silicon_creator_lib_base_sec_mmio = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_base_sec_mmio',
    sources: [
      'sec_mmio.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
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
      sw_silicon_creator_lib_base_mock_abs_mmio
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)
