# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
# -o hw/top_earlgrey

# IP Integration Tests
plic_all_irqs_test_lib = declare_dependency(
  link_with: static_library(
    'plic_all_irqs_test_lib',
    sources: [
      'plic_all_irqs_test.c',
    ],
    dependencies: [
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_dif_adc_ctrl,
      sw_lib_dif_alert_handler,
      sw_lib_dif_aon_timer,
      sw_lib_dif_csrng,
      sw_lib_dif_edn,
      sw_lib_dif_entropy_src,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_gpio,
      sw_lib_dif_hmac,
      sw_lib_dif_i2c,
      sw_lib_dif_keymgr,
      sw_lib_dif_kmac,
      sw_lib_dif_otbn,
      sw_lib_dif_otp_ctrl,
      sw_lib_dif_pattgen,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rv_plic,
      sw_lib_dif_rv_timer,
      sw_lib_dif_sensor_ctrl,
      sw_lib_dif_spi_device,
      sw_lib_dif_spi_host,
      sw_lib_dif_sysrst_ctrl,
      sw_lib_dif_uart,
      sw_lib_dif_usbdev,
      sw_lib_runtime_log,
      sw_lib_testing_rv_plic_testutils,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'plic_all_irqs_test': {
    'library': plic_all_irqs_test_lib,
  }
}

alert_test_lib = declare_dependency(
  link_with: static_library(
    'alert_test_lib',
    sources: [hw_ip_alert_handler_reg_h,
    'alert_test.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_mmio,
      sw_lib_testing_alert_handler_testutils,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_log,
      sw_lib_testing_test_status,
      sw_lib_dif_adc_ctrl,
      sw_lib_dif_aes,
      sw_lib_dif_aon_timer,
      sw_lib_dif_clkmgr,
      sw_lib_dif_csrng,
      sw_lib_dif_edn,
      sw_lib_dif_entropy_src,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_gpio,
      sw_lib_dif_hmac,
      sw_lib_dif_i2c,
      sw_lib_dif_keymgr,
      sw_lib_dif_kmac,
      sw_lib_dif_lc_ctrl,
      sw_lib_dif_otbn,
      sw_lib_dif_otp_ctrl,
      sw_lib_dif_pattgen,
      sw_lib_dif_pinmux,
      sw_lib_dif_pwm,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_dif_rv_plic,
      sw_lib_dif_rv_timer,
      sw_lib_dif_sensor_ctrl,
      sw_lib_dif_spi_device,
      sw_lib_dif_spi_host,
      sw_lib_dif_sram_ctrl,
      sw_lib_dif_sysrst_ctrl,
      sw_lib_dif_uart,
      sw_lib_dif_usbdev,
    ],
  ),
)
sw_tests += {
  'alert_test': {
    'library': alert_test_lib,
  }
}
