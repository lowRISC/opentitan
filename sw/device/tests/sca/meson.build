# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('sca_prng_unittest', executable(
  'sca_prng_unittest',
  sources: [
    meson.source_root() / 'sw/device/sca/lib/prng.c',
    'sca_prng_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
  ],
  native: true,
))
