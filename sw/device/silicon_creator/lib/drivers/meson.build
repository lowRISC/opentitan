# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    sw_lib_base_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

