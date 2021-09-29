# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Random number generator.
sw_lib_testing_rand_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_rand_testutils',
    sources: ['rand_testutils.c'],
  ),
)

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

# aon_timer test utilities.
sw_lib_testing_aon_timer_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_aon_timer_testutils',
    sources: [
      'aon_timer_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_aon_timer,
      top_earlgrey,
    ],
  ),
)

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
    ],
  ),
)

# hardware entropy complex (entropy_src, csrng, edn) test utilities.
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
      top_earlgrey,
    ],
  ),
)

# pwrmgr test utilities.
sw_lib_testing_pwrmgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_pwrmgr_testutils',
    sources: [
      'pwrmgr_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_pwrmgr,
    ],
  ),
)

# rstmgr test utilities.
sw_lib_testing_rstmgr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_rstmgr_testutils',
    sources: [
      'rstmgr_testutils.c'
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_rstmgr,
    ],
  ),
)

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
    ],
  ),
)

sw_lib_testing_sram_ctrl_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_sram_ctrl_testutils',
    sources: [
      hw_ip_sram_ctrl_reg_h,
      'sram_ctrl_testutils.c'
    ],
    dependencies: [
      sw_lib_dif_sram_ctrl,
      sw_lib_runtime_log,
    ],
  ),
)

subdir('test_framework')
