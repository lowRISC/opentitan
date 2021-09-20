# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Autogen UART DIF library
sw_lib_dif_autogen_uart = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_uart',
    sources: [
      hw_ip_uart_reg_h,
      'dif_uart_autogen.c',
    ],
    include_directories: include_directories('../'),
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# Autogen Lifecycle Controller DIF library
sw_lib_dif_autogen_lc_ctrl = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_lc_ctrl',
    sources: [
      hw_ip_lc_ctrl_reg_h,
      'dif_lc_ctrl_autogen.c',
    ],
    include_directories: include_directories('../'),
    dependencies: [
      sw_lib_mmio,
    ],
  )
)
