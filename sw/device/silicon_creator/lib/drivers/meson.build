# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM lifecycle driver
sw_silicon_creator_lib_driver_lifecycle = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_lifecycle',
    sources: [
      hw_ip_lc_ctrl_reg_h,
      'lifecycle.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_sec_mmio,
      sw_lib_bitfield,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_lifecycle_unittest', executable(
    'sw_silicon_creator_lib_driver_lifecycle_unittest',
    sources: [
      'lifecycle_unittest.cc',
      hw_ip_lc_ctrl_reg_h,
      'lifecycle.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_silicon_creator_lib_base_mock_sec_mmio,
      sw_lib_testing_hardened,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

# Mask ROM hmac driver
sw_silicon_creator_lib_driver_hmac = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'hmac.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_lib_mem,
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
      sw_lib_testing_mock_abs_mmio,
      sw_lib_testing_memory,
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
      sw_lib_abs_mmio,
      sw_silicon_creator_lib_base_sec_mmio,
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
      sw_lib_testing_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
    ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_keymgr_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_keymgr_functest',
    sources: [
      hw_ip_keymgr_reg_h,
      'keymgr_functest.c',
    ],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_kmac,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_otp_ctrl,
      sw_lib_testing_flash_ctrl_testutils,
      sw_lib_testing_pwrmgr_testutils,
      sw_silicon_creator_lib_base_sec_mmio,
      sw_silicon_creator_lib_driver_keymgr,
      sw_silicon_creator_lib_driver_lifecycle,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_keymgr_functest': {
    'library': sw_silicon_creator_lib_driver_keymgr_functest,
  }
}

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
      sw_lib_abs_mmio,
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
      sw_lib_testing_mock_abs_mmio,
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
      sw_silicon_creator_lib_base_sec_mmio,
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
      sw_silicon_creator_lib_base_mock_sec_mmio,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

# Mask ROM retention SRAM driver
sw_silicon_creator_lib_driver_retention_sram = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_retention_sram',
    sources: [
      hw_ip_sram_ctrl_reg_h,
      'retention_sram.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_retention_sram_unittest', executable(
    'sw_silicon_creator_lib_driver_retention_sram_unittest',
    sources: [
      'retention_sram_unittest.cc',
      hw_ip_sram_ctrl_reg_h,
      'retention_sram.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_retention_sram_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_retention_sram_functest',
    sources: ['retention_sram_functest.c'],
    dependencies: [
      sw_silicon_creator_lib_driver_retention_sram,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_retention_sram_functest': {
    'library': sw_silicon_creator_lib_driver_retention_sram_functest,
  }
}

# Mask ROM rng driver
sw_silicon_creator_lib_driver_rnd = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_rnd',
    sources: [
      hw_ip_ibex_reg_h,
      hw_ip_otp_ctrl_reg_h,
      'rnd.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_silicon_creator_lib_driver_otp,
    ],
  ),
)

sw_silicon_creator_lib_driver_rnd_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_rnd_functest',
    sources: ['rnd_functest.c'],
    dependencies: [
      sw_silicon_creator_lib_driver_rnd,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_rnd_functest': {
    'library': sw_silicon_creator_lib_driver_rnd_functest,
  }
}

# Mask ROM rstmgr driver
sw_silicon_creator_lib_driver_rstmgr = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_rstmgr',
    sources: [
      hw_ip_rstmgr_reg_h,
      'rstmgr.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
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
      sw_lib_testing_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)


sw_silicon_creator_lib_driver_rstmgr_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_rstmgr_functest',
    sources: [
      hw_ip_rstmgr_reg_h,
      'rstmgr_functest.c'
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_silicon_creator_lib_driver_rstmgr,
      sw_silicon_creator_lib_driver_retention_sram,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_rstmgr_functest': {
    'library': sw_silicon_creator_lib_driver_rstmgr_functest,
  }
}

# Mask ROM alert handler driver
sw_silicon_creator_lib_driver_alert = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_alert',
    sources: [
      hw_ip_alert_handler_reg_h,
      'alert.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_sec_mmio,
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
      sw_silicon_creator_lib_base_mock_sec_mmio,
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
      sw_lib_abs_mmio,
      sw_lib_bitfield,
      sw_silicon_creator_lib_base_sec_mmio,
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

# Mask ROM pinmux driver
sw_silicon_creator_lib_driver_pinmux = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_pinmux',
    sources: [
      hw_top_earlgrey_pinmux_reg_h,
      hw_ip_otp_ctrl_reg_h,
      'pinmux.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_lib_hardened,
      sw_silicon_creator_lib_driver_otp,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_pinmux_unittest', executable(
    'sw_silicon_creator_lib_driver_pinmux_unittest',
    sources: [
      'pinmux_unittest.cc',
      hw_top_earlgrey_pinmux_reg_h,
      hw_ip_otp_ctrl_reg_h,
      'pinmux.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_mock_abs_mmio,
      sw_lib_testing_hardened,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
  ),
  suite: 'mask_rom',
)

# Mask ROM watchdog driver
sw_silicon_creator_lib_driver_watchdog = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_watchdog',
    sources: [
      hw_ip_aon_timer_reg_h,
      hw_ip_otp_ctrl_reg_h,
      hw_ip_pwrmgr_reg_h,
      'watchdog.c',
    ],
    dependencies: [
      sw_lib_mmio,
      sw_silicon_creator_lib_base_sec_mmio,
      sw_silicon_creator_lib_driver_lifecycle,
      sw_silicon_creator_lib_driver_otp,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_watchdog_unittest', executable(
    'sw_silicon_creator_lib_driver_watchdog_unittest',
    sources: [
      'watchdog_unittest.cc',
      hw_ip_aon_timer_reg_h,
      hw_ip_otp_ctrl_reg_h,
      hw_ip_pwrmgr_reg_h,
      'watchdog.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_hardened,
      sw_silicon_creator_lib_base_mock_sec_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

# Mask ROM otbn driver
sw_silicon_creator_lib_driver_otbn = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_otbn',
    sources: [
      hw_ip_otbn_reg_h,
      'otbn.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_otbn_unittest', executable(
    'sw_silicon_creator_lib_driver_otbn_unittest',
    sources: [
      'otbn_unittest.cc',
      hw_ip_otbn_reg_h,
      'otbn.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_mock_abs_mmio,
      sw_lib_testing_hardened,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DMOCK_ABS_MMIO', '-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

sw_silicon_creator_lib_driver_watchdog_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_watchdog_functest',
    sources: [
      hw_ip_rstmgr_reg_h,
      'watchdog_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_driver_retention_sram,
      sw_silicon_creator_lib_driver_rstmgr,
      sw_silicon_creator_lib_driver_watchdog,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_driver_watchdog_functest': {
    'library': sw_silicon_creator_lib_driver_watchdog_functest,
  }
}

# Mask ROM flash_ctrl driver
sw_silicon_creator_lib_driver_flash_ctrl = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_flash_ctrl',
    sources: [
      hw_ip_flash_ctrl_reg_h,
      hw_ip_otp_ctrl_reg_h,
      'flash_ctrl.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_silicon_creator_lib_base_sec_mmio,
      sw_silicon_creator_lib_driver_otp,
      sw_lib_hardened,
      sw_lib_mem,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_flash_ctrl_unittest', executable(
    'sw_silicon_creator_lib_driver_flash_ctrl_unittest',
    sources: [
      'flash_ctrl_unittest.cc',
      hw_ip_flash_ctrl_reg_h,
      hw_ip_otp_ctrl_reg_h,
      'flash_ctrl.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_mock_abs_mmio,
      sw_silicon_creator_lib_base_mock_sec_mmio,
      sw_lib_testing_hardened,
      sw_lib_testing_memory,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO', '-DMOCK_SEC_MMIO', '-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DMOCK_ABS_MMIO', '-DMOCK_SEC_MMIO', '-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

# Mask ROM spi_device driver
sw_silicon_creator_lib_driver_spi_device = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_spi_device',
    sources: [
      hw_ip_spi_device_reg_h,
      hw_ip_flash_ctrl_reg_h,
      'spi_device.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_lib_mem,
    ],
  ),
)

# Mask ROM ibex driver
sw_silicon_creator_lib_driver_ibex = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_ibex',
    sources: [
      hw_ip_ibex_reg_h,
      'ibex.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
    ],
  ),
)

test('sw_silicon_creator_lib_driver_spi_device_unittest', executable(
    'sw_silicon_creator_lib_driver_spi_device_unittest',
    sources: [
      'spi_device_unittest.cc',
      hw_ip_spi_device_reg_h,
      hw_ip_flash_ctrl_reg_h,
      'spi_device.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_memory,
      sw_lib_testing_mock_abs_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_ABS_MMIO'],
    cpp_args: ['-DMOCK_ABS_MMIO'],
    ),
  suite: 'mask_rom',
)
