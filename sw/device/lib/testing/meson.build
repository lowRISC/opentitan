# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('test_framework')

# Check macros
sw_lib_testing_check = declare_dependency(
  dependencies: [
    sw_lib_mem,
    sw_lib_dif_base,
    sw_lib_runtime_hart,
    sw_lib_runtime_log,
    sw_lib_testing_test_status,
  ],
)

# Random number generator test utilities
sw_lib_testing_rand_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_rand_testutils',
    sources: ['rand_testutils.c'],
    dependencies: [
      sw_lib_testing_check,
    ],
  ),
)

# aes test utilities
sw_lib_testing_aes_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_aes_testutils',
    sources: [
      'aes_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_aes,
      sw_lib_runtime_ibex,
    ],
  ),
)

# alert_handler test utilities
sw_lib_testing_alert_handler_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_alert_handler_testutils',
    sources: [
      hw_ip_alert_handler_reg_h,
      'alert_handler_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_alert_handler,
      sw_lib_dif_base,
      sw_lib_testing_check,
    ],
  ),
)

# aon_timer test utilities
sw_lib_testing_aon_timer_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_aon_timer_testutils',
    sources: [
      'aon_timer_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_aon_timer,
      sw_lib_testing_check,
      top_earlgrey,
    ],
  ),
)

# clkmgr test utilities
sw_lib_testing_clkmgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_clkmgr_testutils',
    sources: [
      hw_ip_clkmgr_reg_h,
      'clkmgr_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_runtime_ibex,
      sw_lib_testing_check,
    ],
  ),
)

# hardware entropy complex (entropy_src, csrng, edn) test utilities
sw_lib_testing_entropy_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_entropy_testutils',
    sources: [
      hw_ip_edn_reg_h,
      'entropy_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_entropy_src,
      sw_lib_dif_csrng,
      sw_lib_testing_check,
      top_earlgrey,
    ],
  ),
)

# flash_ctrl test utilities
sw_lib_testing_flash_ctrl_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_flash_ctrl_testutils',
    sources: [
      'flash_ctrl_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_dif_flash_ctrl,
      sw_lib_testing_check,
    ],
  ),
)

# pinmux test utilities
sw_lib_testing_pinmux_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_pinmux_testutils',
    sources: [
      hw_top_earlgrey_pinmux_reg_h,
      'pinmux_testutils.c',
    ],
    dependencies: [
      sw_lib_dif_pinmux,
      sw_lib_testing_check,
      top_earlgrey,
    ]
  )
)

# pwrmgr test utilities
sw_lib_testing_pwrmgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_pwrmgr_testutils',
    sources: [
      'pwrmgr_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_pwrmgr,
      sw_lib_testing_check,
    ],
  ),
)

# rstmgr test utilities
sw_lib_testing_rstmgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_rstmgr_testutils',
    sources: [
      'rstmgr_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_rstmgr,
      sw_lib_testing_check,
    ],
  ),
)

# rv_plic test utilities
sw_lib_testing_rv_plic_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_rv_plic_testutils',
    sources: [
      hw_ip_edn_reg_h,
      'rv_plic_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_rv_plic,
      sw_lib_runtime_log,
      sw_lib_testing_rand_testutils,
      sw_lib_testing_check,
    ],
  ),
)

# sram_ctrl test utilities
sw_lib_testing_sram_ctrl_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_sram_ctrl_testutils',
    sources: [
      'sram_ctrl_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_sram_ctrl,
      sw_lib_runtime_log,
      sw_lib_testing_check,
    ],
  ),
)

# otp_ctrl test utilities
sw_lib_testing_otp_ctrl_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_otp_ctrl_testutils',
    sources: [
      hw_ip_otp_ctrl_reg_h,
      'otp_ctrl_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_otp_ctrl,
      sw_lib_runtime_ibex,
      sw_lib_testing_check,
    ],
  ),
)

# lc_ctrl test utilities
sw_lib_testing_lc_ctrl_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_lc_ctrl_testutils',
    sources: [
      hw_ip_lc_ctrl_reg_h,
      'lc_ctrl_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_lc_ctrl,
      sw_lib_testing_check,
    ],
  ),
)

# HMAC test utilities
sw_lib_testing_hmac_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_hmac_testutils',
    sources: [
      hw_ip_hmac_reg_h,
      'hmac_testutils.c',
    ],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_runtime_log,
      sw_lib_testing_check,
    ],
  ),
)

# keymgr test utilities
sw_lib_testing_keymgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_keymgr_testutils',
    sources: [
      hw_ip_keymgr_reg_h,
      'keymgr_testutils.c',
    ],
    dependencies: [
      sw_lib_dif_keymgr,
      sw_lib_runtime_log,
      sw_lib_testing_check,
    ],
  ),
)

subdir('autogen')
subdir('test_rom')
