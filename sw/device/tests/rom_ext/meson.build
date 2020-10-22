# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All tests added to this dictionary will result in build targets that have
# names starting `sw/device/tests/rom_ext/<test_name>`. They will not contain
# the subdirectory name, because the build targets are really declared at the
# bottom of this file, rather than in the subdirectories.
rom_ext_tests = {
  # 'test_name': test_lib,
}

test('rom_ext_parser_unittest', executable(
  'rom_ext_parser_unittest',
  sources: [
    'rom_ext_parser_unittest.cc',
    meson.source_root() / 'sw/device/rom_exts/rom_ext_manifest_parser.c',
    rom_exts_manifest_offsets_header,
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
    sw_lib_testing_bitfield,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))
