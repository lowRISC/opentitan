# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM hmac driver
sw_silicon_creator_lib_driver_hmac = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'hmac.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_hmac_unittest', executable(
    'sw_silicon_creator_lib_driver_hmac_unittest',
    sources: [
      'hmac_unittest.cc',
      hw_ip_hmac_reg_h,
      'hmac.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
    ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_hmac_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_hmac_functest',
    sources: ['hmac_functest.c'],
    dependencies: [
      sw_silicon_creator_lib_driver_hmac,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_hmac_functest': {
    'library': sw_silicon_creator_lib_driver_hmac_functest,
  }
}

# Mask ROM keymgr driver
sw_silicon_creator_lib_driver_keymgr = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_keymgr',
    sources: [
      hw_ip_keymgr_reg_h,
      'keymgr.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_keymgr_unittest', executable(
    'sw_silicon_creator_lib_driver_keymgr_unittest',
    sources: [
      'keymgr_unittest.cc',
      hw_ip_keymgr_reg_h,
      'keymgr.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
    ),
  suite: 'mask_rom',
)

# Mask ROM uart driver
sw_silicon_creator_lib_driver_uart = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_uart',
    sources: [
      hw_ip_uart_reg_h,
      'uart.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_uart_unittest', executable(
    'sw_silicon_creator_lib_driver_uart_unittest',
    sources: [
      'uart_unittest.cc',
      hw_ip_uart_reg_h,
      'uart.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_uart_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_uart_functest',
    sources: ['uart_functest.c'],
    dependencies: [
      sw_silicon_creator_lib_driver_uart,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_uart_functest': {
    'library': sw_silicon_creator_lib_driver_uart_functest,
  }
}


# Mask OTP uart driver
sw_silicon_creator_lib_driver_otp = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_otp',
    sources: [
      hw_ip_otp_ctrl_reg_h,
      'otp.c',
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_otp_unittest', executable(
    'sw_silicon_creator_lib_driver_otp_unittest',
    sources: [
      'otp_unittest.cc',
      hw_ip_otp_ctrl_reg_h,
      'otp.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_base_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
    ),
  suite: 'mask_rom',
)

# Mask ROM rstmgr driver
sw_silicon_creator_lib_driver_rstmgr = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_rstmgr',
    sources: [
      hw_ip_rstmgr_reg_h,
      'rstmgr.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_rstmgr_unittest', executable(
    'sw_silicon_creator_lib_driver_rstmgr_unittest',
    sources: [
      'rstmgr_unittest.cc',
      hw_ip_rstmgr_reg_h,
      'rstmgr.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)

# Mask ROM alert handler driver
sw_silicon_creator_lib_driver_alert = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_alert',
    sources: [
      hw_ip_alert_handler_reg_h,
      'alert.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_alert_unittest', executable(
    'sw_silicon_creator_lib_driver_alert_unittest',
    sources: [
      'alert_unittest.cc',
      hw_ip_alert_handler_reg_h,
      'alert.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_alert_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_alert_functest',
    sources: [
      hw_ip_rstmgr_reg_h,
      hw_ip_otp_ctrl_reg_h,
      hw_ip_alert_handler_reg_h,
      hw_ip_flash_ctrl_reg_h,
      'alert_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_driver_alert,
      sw_silicon_creator_lib_driver_rstmgr,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_alert_functest': {
    'library': sw_silicon_creator_lib_driver_alert_functest,
  }
}
