# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
subdir('base')
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

# Manifest section for boot stage images stored in flash.
sw_silicon_creator_lib_manifest_section = declare_dependency(
  # Using link_whole so that the .manifest section is created even if a boot
  # stage doesn't use kManifest.
  link_whole: static_library(
    'sw_silicon_creator_lib_manifest_section',
    sources: [
      'manifest.S',
    ],
  ),
)

# Manifest library.
sw_silicon_creator_lib_manifest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_manifest',
    sources: [
      'manifest.c',
    ],
  ),
)

# Defined separately for sigverify_keys unit tests.
sw_silicon_creator_lib_sigverify_sources_for_boot_stage_tests = files([
  'sigverify_mod_exp_ibex.c',
  'sigverify.c',
])

# Signature verification.
sw_silicon_creator_lib_sigverify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_sigverify',
    sources: [
      'sigverify_mod_exp_ibex.c',
      'sigverify.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_driver_hmac,
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

test('sw_silicon_creator_lib_manifest_unittest', executable(
    'sw_silicon_creator_lib_manifest_unittest',
    sources: [
      'manifest_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

test('sw_silicon_creator_mask_rom_sigverify_mod_exp_ibex_unittest', executable(
    'sw_silicon_creator_mask_rom_sigverify_mod_exp_ibex_unittest',
    sources: [
      'sigverify_mod_exp_ibex.c',
      'sigverify_mod_exp_ibex_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

test('sw_silicon_creator_lib_sigverify_unittest', executable(
    'sw_silicon_creator_lib_sigverify_unittest',
    sources: [
      'sigverify_unittest.cc',
      'sigverify.c',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_sigverify_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_sigverify_functest',
    sources: [
      'sigverify_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_sigverify_functest': {
    'library': sw_silicon_creator_lib_sigverify_functest,
  }
}
