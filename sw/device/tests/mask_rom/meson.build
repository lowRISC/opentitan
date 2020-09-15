# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('mask_rom_sig_verify_unittest', executable(
  'mask_rom_sig_verify_unittest',
  sources: [
    meson.source_root()/'sw'/'device'/'mask_rom'/'sig_verify.c',
    'mask_rom_sig_verify_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
  ],
  native: true,
))
