# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('dif_spi_device_unittest', executable(
  'dif_spi_device_unittest',
  sources: [
    hw_ip_spi_device_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_spi_device.c',
    'dif_spi_device_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_uart_unittest', executable(
  'dif_uart_unittest',
  sources: [
    'dif_uart_unittest.cc',
    meson.source_root() / 'sw/device/lib/dif/dif_uart.c',
    hw_ip_uart_reg_h,
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_plic_unittest', executable(
  'dif_plic_unittest',
  sources: [
    hw_top_earlgrey_rv_plic_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_plic.c',
    'dif_plic_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_i2c_unittest', executable(
  'dif_i2c_unittest',
  sources: [
    hw_ip_i2c_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_i2c.c',
    'dif_i2c_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_gpio_unittest', executable(
  'dif_gpio_unittest',
  sources: [
    hw_ip_gpio_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_gpio.c',
    'dif_gpio_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_rv_timer_unittest', executable(
  'dif_rv_timer_unittest',
  sources: [
    hw_ip_rv_timer_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_rv_timer.c',
    'dif_rv_timer_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_otbn_unittest', executable(
  'dif_otbn_unittest',
  sources: [
    'dif_otbn_unittest.cc',
    meson.source_root() / 'sw/device/lib/dif/dif_otbn.c',
    hw_ip_otbn_reg_h,
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_pwrmgr_unittest', executable(
  'dif_pwrmgr_unittest',
  sources: [
    hw_ip_pwrmgr_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_pwrmgr.c',
    'dif_pwrmgr_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_rstmgr_unittest', executable(
  'dif_rstmgr_unittest',
  sources: [
    'dif_rstmgr_unittest.cc',
    meson.source_root() / 'sw/device/lib/dif/dif_rstmgr.c',
    hw_ip_rstmgr_reg_h,
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_alert_handler_unittest', executable(
  'dif_alert_handler_unittest',
  sources: [
    'dif_alert_handler_unittest.cc',
    meson.source_root() / 'sw/device/lib/dif/dif_alert_handler.c',
    hw_ip_alert_handler_reg_h,
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_otp_ctrl_unittest', executable(
  'dif_otp_ctrl_unittest',
  sources: [
    hw_ip_otp_ctrl_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_otp_ctrl.c',
    'dif_otp_ctrl_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_lc_ctrl_unittest', executable(
  'dif_lc_ctrl_unittest',
  sources: [
    hw_ip_lc_ctrl_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_lc_ctrl.c',
    'dif_lc_ctrl_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_aes_test', executable(
  'dif_aes_test',
  sources: [
    hw_ip_aes_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_aes.c',
    'dif_aes_test.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'], 
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_clkmgr_unittest', executable(
  'dif_clkmgr_unittest',
  sources: [
    hw_ip_clkmgr_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_clkmgr.c',
    'dif_clkmgr_unittest.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

dif_plic_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_plic_smoketest_lib',
    sources: ['dif_plic_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_dif_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'dif_plic_smoketest': {
    'library': dif_plic_smoketest_lib,
  }
}

dif_uart_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_uart_smoketest_lib',
    sources: ['dif_uart_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_uart_smoketest': {
    'library': dif_uart_smoketest_lib,
  }
}

dif_rv_timer_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_rv_timer_smoketest_lib',
    sources: ['dif_rv_timer_smoketest.c'],
    dependencies: [
      sw_lib_dif_rv_timer,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_irq,
    ],
  ),
)
sw_tests += {
  'dif_rv_timer_smoketest': {
    'library': dif_rv_timer_smoketest_lib,
  }
}

dif_hmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_hmac_smoketest_lib',
    sources: ['dif_hmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_hmac_smoketest': {
    'library': dif_hmac_smoketest_lib,
  }
}

dif_rstmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_rstmgr_smoketest_lib',
    sources: ['dif_rstmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_rstmgr_smoketest': {
    'library': dif_rstmgr_smoketest_lib,
  }
}

dif_otbn_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_otbn_smoketest_lib',
    sources: ['dif_otbn_smoketest.c'],
    dependencies: [
      sw_lib_dif_otbn,
      sw_lib_runtime_hart,
      sw_lib_runtime_otbn,
      top_earlgrey,
      sw_otbn['barrett384']['rv32embed_dependency'],
      sw_otbn['err_test']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'dif_otbn_smoketest': {
    'library': dif_otbn_smoketest_lib,
  }
}

dif_otp_ctrl_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_otp_ctrl_smoketest_lib',
    sources: ['dif_otp_ctrl_smoketest.c'],
    dependencies: [
      sw_lib_dif_otp_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_otp_ctrl_smoketest': {
    'library': dif_otp_ctrl_smoketest_lib,
  }
}

dif_gpio_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_gpio_smoketest_lib',
    sources: ['dif_gpio_smoketest.c'],
    dependencies: [
      sw_lib_dif_gpio,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_gpio_smoketest': {
    'library': dif_gpio_smoketest_lib,
  }
}

dif_aes_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_aes_smoketest_lib',
    sources: ['dif_aes_smoketest.c'],
    dependencies: [
      sw_lib_dif_aes,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'dif_aes_smoketest': {
    'library': dif_aes_smoketest_lib,
  }
}

dif_clkmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_clkmgr_smoketest_lib',
    sources: ['dif_clkmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_clkmgr_smoketest': {
    'library': dif_clkmgr_smoketest_lib,
  }
}
