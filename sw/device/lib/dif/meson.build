# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# UART DIF library (dif_uart)
dif_uart = declare_dependency(
  sources: [hw_ip_uart_reg_h],
  link_with: static_library(
    'uart_ot',
    sources: [
      hw_ip_uart_reg_h,
      'dif_uart.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ]
  )
)

# PLIC DIF library (dif_plic)
dif_plic = declare_dependency(
  link_with: static_library(
    'dif_plic_ot',
    sources: ['dif_plic.c'],
    dependencies: [sw_lib_mmio]
  )
)
