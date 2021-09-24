# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Autogen AES DIF library
sw_lib_dif_autogen_aes = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_aes',
    sources: [
      hw_ip_aes_reg_h,
      'dif_aes_autogen.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# Autogen Alert Handler DIF library
sw_lib_dif_autogen_alert_handler = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_alert_handler',
    sources: [
      hw_ip_alert_handler_reg_h,
      'dif_alert_handler_autogen.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# Autogen HMAC DIF library
sw_lib_dif_autogen_hmac = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'dif_hmac_autogen.c',
    ],
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
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# Autogen UART DIF library
sw_lib_dif_autogen_uart = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_autogen_uart',
    sources: [
      hw_ip_uart_reg_h,
      'dif_uart_autogen.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)
