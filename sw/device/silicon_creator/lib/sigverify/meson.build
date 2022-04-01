# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Defined separately for sigverify_keys unit tests.
sw_silicon_creator_lib_sigverify_sources_for_boot_stage_tests = files([
  'mod_exp_ibex.c',
  'sigverify.c',
])

# Signature verification.
sw_silicon_creator_lib_sigverify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_sigverify',
    sources: [
      'mod_exp_ibex.c',
      'mod_exp_otbn.c',
      'sigverify.c',
      hw_ip_otp_ctrl_reg_h,
    ],
    dependencies: [
      sw_silicon_creator_lib_driver_otp,
      sw_silicon_creator_lib_driver_lifecycle,
      sw_lib_bitfield,
      sw_lib_hardened,
      sw_silicon_creator_lib_otbn_util,
      sw_otbn['run_rsa_verify_3072_rr_modexp']['rv32embed_dependency'],
    ],
  ),
)

test('sw_silicon_creator_mask_rom_mod_exp_ibex_unittest', executable(
    'sw_silicon_creator_mask_rom_mod_exp_ibex_unittest',
    sources: [
      'mod_exp_ibex.c',
      'mod_exp_ibex_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_memory,
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
      'mod_exp_ibex_mock.cc',
      'mod_exp_otbn_mock.cc',
      hw_ip_otp_ctrl_reg_h,
      hw_ip_flash_ctrl_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
      sw_lib_testing_hardened,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
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
      sw_silicon_creator_lib_driver_hmac,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_sigverify_functest': {
    'library': sw_silicon_creator_lib_sigverify_functest,
  }
}

sw_silicon_creator_lib_sigverify_dynamic_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_sigverify_dynamic_functest',
    sources: [
      'sigverify_dynamic_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_sigverify_dynamic_functest': {
    'library': sw_silicon_creator_lib_sigverify_dynamic_functest,
  }
}

sw_silicon_creator_lib_mod_exp_ibex_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_mod_exp_ibex_functest',
    sources: [
      'mod_exp_ibex_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_mod_exp_ibex_functest': {
    'library': sw_silicon_creator_lib_mod_exp_ibex_functest,
  }
}

sw_silicon_creator_lib_mod_exp_otbn_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_mod_exp_otbn_functest',
    sources: [
      'mod_exp_otbn_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_mod_exp_otbn_functest': {
    'library': sw_silicon_creator_lib_mod_exp_otbn_functest,
  }
}