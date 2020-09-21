# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('runtime_print_unittest', executable(
  'runtime_print_unittest',
  sources: [
    meson.source_root() / 'sw/device/lib/runtime/print.c',
    'print_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
  ],
  native: true,
))
