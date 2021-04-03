# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('rsa_verify_unittest', executable(
  'rsa_verify_unittest',
  sources: [
    meson.source_root() / 'sw/device/silicon_creator/mask_rom/rsa_verify.c',
    'rsa_verify_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
  ],
  native: true,
))
