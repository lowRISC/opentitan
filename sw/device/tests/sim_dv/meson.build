# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

uart_tx_rx_test_lib = declare_dependency(
  link_with: static_library(
    'uart_tx_rx_test_lib',
    sources: ['uart_tx_rx_test.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_dif_plic,
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
      sw_lib_dif_plic,
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

spi_tx_rx_test_lib = declare_dependency(
  link_with: static_library(
    'spi_tx_rx_test_lib',
    sources: ['spi_tx_rx_test.c'],
    dependencies: [
      sw_lib_dif_spi_device,
      sw_lib_dif_plic,
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
