# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
subdir('drivers')

# Mask ROM fake dependencies.  These are temporary dependencies until we
# refactor or copy the other libraries we need (e.g. `runtime`).
sw_silicon_creator_lib_fake_deps = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_fake_deps',
    sources: [
      'fake_deps.c',
    ],
    dependencies: [
    ],
  ),
)

test('sw_silicon_creator_lib_error_unittest', executable(
    'sw_silicon_creator_lib_error_unittest',
    sources: [
      'error_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

