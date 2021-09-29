# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('autogen')

# Clock Manager DIF Library (dif_clkmgr)
sw_lib_dif_clkmgr = declare_dependency(
  link_with: static_library(
    'clkmgr_ot',
    sources: [
      hw_ip_clkmgr_reg_h,
      'dif_clkmgr.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

test('dif_clkmgr_unittest', executable(
    'dif_clkmgr_unittest',
    sources: [
      hw_ip_clkmgr_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_clkmgr.c',
      'dif_clkmgr_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# CSRNG DIF Library (dif_csrng)
sw_lib_dif_csrng = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_csrng',
    sources: [
      hw_ip_csrng_reg_h,
      'dif_csrng.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_autogen_csrng,
    ],
  )
)

test('dif_csrng_unittest', executable(
    'dif_csrng_unittest',
    sources: [
      'dif_csrng_unittest.cc',
      'autogen/dif_csrng_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_csrng.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_csrng_autogen.c',
      hw_ip_csrng_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# EDN DIF Library (dif_csrng)
sw_lib_dif_edn = declare_dependency(
  link_with: static_library(
    'edn_ot',
    sources: [
      hw_ip_edn_reg_h,
      'dif_edn.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_autogen_edn,
    ],
  )
)

test('dif_edn_unittest', executable(
    'dif_edn_unittest',
    sources: [
      'autogen/dif_edn_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_edn.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_edn_autogen.c',
      hw_ip_edn_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_uart,
    ],
  )
)

test('dif_uart_unittest', executable(
    'dif_uart_unittest',
    sources: [
      'dif_uart_unittest.cc',
      'autogen/dif_uart_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_uart.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_uart_autogen.c',
      hw_ip_uart_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# PLIC DIF library (dif_rv_plic)
sw_lib_dif_rv_plic = declare_dependency(
  link_with: static_library(
    'dif_rv_plic_ot',
    sources: [
      hw_top_earlgrey_rv_plic_reg_h,
      'dif_rv_plic.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

test('dif_rv_plic_unittest', executable(
    'dif_rv_plic_unittest',
    sources: [
      hw_top_earlgrey_rv_plic_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_rv_plic.c',
      'dif_rv_plic_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_gpio,
    ],
  )
)

test('dif_gpio_unittest', executable(
    'dif_gpio_unittest',
    sources: [
      'dif_gpio_unittest.cc',
      'autogen/dif_gpio_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_gpio.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_gpio_autogen.c',
      hw_ip_gpio_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_spi_device_unittest', executable(
    'dif_spi_device_unittest',
    sources: [
      hw_ip_spi_device_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_spi_device.c',
      'dif_spi_device_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_rv_timer_unittest', executable(
    'dif_rv_timer_unittest',
    sources: [
      hw_ip_rv_timer_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_rv_timer.c',
      'dif_rv_timer_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_i2c,
    ],
  )
)

test('dif_i2c_unittest', executable(
    'dif_i2c_unittest',
    sources: [
      'dif_i2c_unittest.cc',
      'autogen/dif_i2c_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_i2c.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_i2c_autogen.c',
      hw_ip_i2c_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_hmac,
    ],
  )
)

test('dif_hmac_unittest', executable(
    'dif_hmac_unittest',
    sources: [
      #'dif_hmac_unittest.cc',
      'autogen/dif_hmac_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/base/memory.c',
      meson.source_root() / 'sw/device/lib/dif/dif_hmac.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_hmac_autogen.c',
      hw_ip_hmac_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# KMAC device DIF library
sw_lib_dif_kmac = declare_dependency(
  link_with: static_library(
    'sw_dif_kmac',
    sources: [
      hw_ip_kmac_reg_h,
      'dif_kmac.c'
    ],
    dependencies: [
      sw_lib_bitfield,
      sw_lib_mmio,
    ],
  )
)

test('dif_kmac_unittest', executable(
    'dif_kmac_unittest',
    sources: [
      'dif_kmac_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_kmac.c',
      hw_ip_kmac_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_otbn_unittest', executable(
    'dif_otbn_unittest',
    sources: [
      'dif_otbn_unittest.cc',
      'autogen/dif_otbn_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_otbn.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_otbn_autogen.c',
      hw_ip_otbn_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',  
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

test('dif_rstmgr_unittest', executable(
    'dif_rstmgr_unittest',
    sources: [
      'dif_rstmgr_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_rstmgr.c',
      hw_ip_rstmgr_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_alert_handler,
    ],
  )
)

test('dif_alert_handler_unittest', executable(
    'dif_alert_handler_unittest',
    sources: [
      'dif_alert_handler_unittest.cc',
      'autogen/dif_alert_handler_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_alert_handler.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_alert_handler_autogen.c',
      hw_ip_alert_handler_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_pwrmgr_unittest', executable(
    'dif_pwrmgr_unittest',
    sources: [
      hw_ip_pwrmgr_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_pwrmgr.c',
      'dif_pwrmgr_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# Key Manager DIF library
sw_lib_dif_keymgr = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_keymgr',
    sources: [
      hw_ip_keymgr_reg_h,
      'dif_keymgr.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
      sw_lib_dif_autogen_keymgr,
    ],
  )
)

test('dif_keymgr_unittest', executable(
    'dif_keymgr_unittest',
    sources: [
      'dif_keymgr_unittest.cc',
      'autogen/dif_keymgr_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_keymgr.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_keymgr_autogen.c',
      hw_ip_keymgr_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_otp_ctrl_unittest', executable(
    'dif_otp_ctrl_unittest',
    sources: [
      hw_ip_otp_ctrl_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_otp_ctrl.c',
      'dif_otp_ctrl_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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
      sw_lib_dif_autogen_lc_ctrl,
    ],
  )
)

test('dif_lc_ctrl_unittest', executable(
    'dif_lc_ctrl_unittest',
    sources: [
      'dif_lc_ctrl_unittest.cc',
      'autogen/dif_lc_ctrl_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_lc_ctrl.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.c',
      hw_ip_lc_ctrl_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
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

test('dif_aon_timer_unittest', executable(
    'dif_aon_timer_unittest',
    sources: [
      hw_ip_aon_timer_reg_h,
      meson.source_root() / 'sw/device/lib/dif/dif_aon_timer.c',
      'dif_aon_timer_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',  
)

# Entropy Source
sw_lib_dif_entropy_src = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_entropy_src',
    sources: [
      hw_ip_entropy_src_reg_h,
      'dif_entropy_src.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
      sw_lib_dif_autogen_entropy_src,
    ],
  )
)

test('dif_entropy_src_unittest', executable(
    'dif_entropy_src_unittest',
    sources: [
      'dif_entropy_src_unittest.cc',
      'autogen/dif_entropy_src_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_entropy_src.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_entropy_src_autogen.c',
      hw_ip_entropy_src_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# AES DIF library
sw_lib_dif_aes = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_aes',
    sources: [
      hw_ip_aes_reg_h,
      'dif_aes.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_autogen_aes,
    ],
  )
)

test('dif_aes_unittest', executable(
    'dif_aes_unittest',
    sources: [
      'dif_aes_unittest.cc',
      'autogen/dif_aes_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_aes.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_aes_autogen.c',
      hw_ip_aes_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)

# Pinmux DIF library
sw_lib_dif_pinmux = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_pinmux',
    sources: [
      hw_top_earlgrey_pinmux_reg_h,
      'dif_pinmux.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_lib_bitfield,
    ],
  )
)

# SRAM Controller library
sw_lib_dif_sram_ctrl = declare_dependency(
  link_with: static_library(
    'sw_lib_dif_sram_ctrl',
    sources: [
      hw_ip_sram_ctrl_reg_h,
      'dif_sram_ctrl.c',
    ],
    dependencies: [sw_lib_mmio],
  )
)

test('dif_sram_ctrl_unittest', executable(
    'dif_sram_ctrl_unittest',
    sources: [
      'dif_sram_ctrl_unittest.cc',
      'autogen/dif_sram_ctrl_autogen_unittest.cc',
      meson.source_root() / 'sw/device/lib/dif/dif_sram_ctrl.c',
      meson.source_root() / 'sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.c',
      hw_ip_sram_ctrl_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  ),
  suite: 'dif',
)
