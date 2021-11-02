# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################
# Smoke Tests
###############################################################################
pwrmgr_usbdev_smoketest_lib = declare_dependency(
  link_with: static_library(
    'pwrmgr_usbdev_smoketest_lib',
    sources: ['pwrmgr_usbdev_smoketest.c'],
    dependencies: [
      sw_lib_dif_pwrmgr,
      sw_lib_usb,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'pwrmgr_usbdev_smoketest': {
    'library': pwrmgr_usbdev_smoketest_lib,
  }
}

###############################################################################
# IP Integration Tests
###############################################################################
uart_tx_rx_test_lib = declare_dependency(
  link_with: static_library(
    'uart_tx_rx_test_lib',
    sources: [
      # TODO, remove it once pinout configuration is provided
      hw_top_earlgrey_pinmux_reg_h,
      'uart_tx_rx_test.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'uart_tx_rx_test': {
    'library': uart_tx_rx_test_lib,
    'dv_frames': true,
  }
}

gpio_test_lib = declare_dependency(
  link_with: static_library(
    'gpio_test_lib',
    sources: ['gpio_test.c'],
    dependencies: [
      sw_lib_dif_gpio,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_pinmux,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'gpio_test': {
    'library': gpio_test_lib,
  }
}

lc_ctrl_transition_test_lib = declare_dependency(
  link_with: static_library(
    'lc_ctrl_transition_test_lib',
    sources: [
      'lc_ctrl_transition_test.c',
    ],
    dependencies: [
      sw_lib_dif_lc_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'lc_ctrl_transition_test': {
    'library': lc_ctrl_transition_test_lib,
  }
}

pwrmgr_main_power_glitch_test_lib = declare_dependency(
  link_with: static_library(
    'pwrmgr_main_power_glitch_test_lib',
    sources: ['pwrmgr_main_power_glitch_test.c'],
    dependencies: [
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_pwrmgr_testutils,
      sw_lib_testing_rstmgr_testutils,
    ],
  ),
)
sw_tests += {
  'pwrmgr_main_power_glitch_test': {
    'library': pwrmgr_main_power_glitch_test_lib,
  }
}

spi_tx_rx_test_lib = declare_dependency(
  link_with: static_library(
    'spi_tx_rx_test_lib',
    sources: ['spi_tx_rx_test.c'],
    dependencies: [
      sw_lib_dif_spi_device,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'spi_tx_rx_test': {
    'library': spi_tx_rx_test_lib,
  }
}
