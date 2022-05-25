# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_sca_lib_sca  = declare_dependency(
  link_with: static_library(
    'lib_sca',
    sources: [
      'sca.c',
      hw_ip_csrng_reg_h,
      hw_ip_edn_reg_h,
      hw_ip_clkmgr_reg_h,
    ],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_dif_gpio,
      sw_lib_dif_pinmux,
      sw_lib_dif_rv_timer,
      sw_lib_dif_uart,
      sw_lib_dif_entropy_src,
      sw_lib_dif_csrng,
      sw_lib_dif_edn,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_testing_pinmux_testutils,
      sw_lib_runtime_log,
    ],
  ),
)

sw_sca_lib_prng = declare_dependency(
  link_with: static_library(
    'lib_prng',
    sources: ['prng.c'],
  ),
)

test('sca_lib_prng_unittest', executable(
    'sca_lib_prng_unittest',
    sources: [
      'prng.c',
      'prng_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'sca',
)

sw_sca_lib_simple_serial = declare_dependency(
  link_with: static_library(
    'lib_simple_serial',
    sources: ['simple_serial.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_print,
      sw_sca_lib_prng,
    ]
  ),
)
