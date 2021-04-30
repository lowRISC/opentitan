# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Secure MMIO module
sw_silicon_creator_lib_base_rom_mmio = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_base_rom_mmio',
    sources: [
      'rom_mmio.c',
    ],
    dependencies: [],
  ),
)

# Mask ROM Secure MMIO module
sw_silicon_creator_lib_base_sec_mmio = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_base_sec_mmio',
    sources: [
      'sec_mmio.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_rom_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_base_sec_mmio_unittest', executable(
    'sw_silicon_creator_lib_base_sec_mmio_unittest',
    sources: [
      'sec_mmio_unittest.cc',
      'sec_mmio.c',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'mask_rom',
)
