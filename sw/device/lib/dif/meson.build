# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Clock Manager DIF Library (dif_clkmgr)
sw_lib_dif_clkmgr = declare_dependency(
  link_with: static_library(
    'clkmgr_ot',
    sources: [
      hw_ip_clkgmr_reg_h,
      'dif_clkmgr.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# UART DIF library (dif_uart)
sw_lib_dif_uart = declare_dependency(
  link_with: static_library(
    'uart_ot',
    sources: [
      hw_ip_uart_reg_h,
      'dif_uart.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# PLIC DIF library (dif_plic)
sw_lib_dif_plic = declare_dependency(
  link_with: static_library(
    'dif_plic_ot',
    sources: [
      hw_top_earlgrey_rv_plic_reg_h,
      'dif_plic.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# GPIO DIF library
sw_lib_dif_gpio = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_gpio',
    sources: [
      hw_ip_gpio_reg_h,
      'dif_gpio.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# SPI DIF library
sw_lib_dif_spi_device = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_spi_device',
    sources: [
      hw_ip_spi_device_reg_h,
      'dif_spi_device.c',
    ],
    dependencies: [sw_lib_mmio],
  )
)

# RISC-V Timer DIF library (dif_rv_timer)
sw_lib_dif_rv_timer = declare_dependency(
  link_with: static_library(
    'dif_rv_timer_ot',
    sources: [
      hw_ip_rv_timer_reg_h,
      'dif_rv_timer.c',
    ],
    dependencies: [
      sw_lib_mmio
    ],
  )
)

# I2C DIF library
sw_lib_dif_i2c = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_i2c',
    sources: [
      hw_ip_i2c_reg_h,
      'dif_i2c.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# USBDEV DIF library (dif_usbdev)
sw_lib_dif_usbdev = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_usbdev',
    sources: [
      hw_ip_usbdev_reg_h,
      'dif_usbdev.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# HMAC device DIF library
sw_lib_dif_hmac = declare_dependency(
  link_with: static_library(
    'sw_dif_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'dif_hmac.c'
    ],
    dependencies: [
      sw_lib_bitfield,
      sw_lib_mmio,
    ],
  )
)

# OTBN DIF library
sw_lib_dif_otbn = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_otbn',
    sources: [
      hw_ip_otbn_reg_h,
      'dif_otbn.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

# Reset Manager DIF library (dif_rstmgr)
sw_lib_dif_rstmgr = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_rstmgr',
    sources: [
      hw_ip_rstmgr_reg_h,
      'dif_rstmgr.c'
    ],
    dependencies: [
      sw_lib_bitfield,
      sw_lib_mmio,
    ],
  )
)

# Alert handler library
sw_lib_dif_alert_handler = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_alert_handler',
    sources: [
      hw_ip_alert_handler_reg_h,
      'dif_alert_handler.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# Power Manager DIF library
sw_lib_dif_pwrmgr = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_pwrmgr',
    sources: [
      hw_ip_pwrmgr_reg_h,
      'dif_pwrmgr.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# OTP controller library
sw_lib_dif_otp_ctrl = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_otp_ctrl',
    sources: [
      hw_ip_otp_ctrl_reg_h,
      'dif_otp_ctrl.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# Lifecycle controller library
sw_lib_dif_lc_ctrl = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_lc_ctrl',
    sources: [
      hw_ip_lc_ctrl_reg_h,
      'dif_lc_ctrl.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# Always-On Timer library
sw_lib_dif_aon_timer = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_aon_timer',
    sources: [
      hw_ip_aon_timer_reg_h,
      'dif_aon_timer.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# AES DIF library
sw_lib_dif_aes = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_aes',
    sources: [
      hw_ip_aes_reg_h,
      'dif_aes.c',
    ],
    dependencies: [sw_lib_mmio],
  )
)
