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

dif_plic_sanitytest_lib = declare_dependency(
  link_with: static_library(
    'dif_plic_sanitytest_lib',
    sources: ['dif_plic_sanitytest.c'],
    dependencies: [
      dif_uart,
      dif_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_base_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
    ],
  ),
)

sw_tests += { 'dif_plic_sanitytest': dif_plic_sanitytest_lib }
