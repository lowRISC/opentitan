# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

test('dif_spi_device_test', executable(
  'dif_spi_device_test',
  sources: [
    hw_ip_spi_device_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_spi_device.c',
    'dif_spi_device_test.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'],
  cpp_args: ['-DMOCK_MMIO'],
))

test('dif_uart_test', executable(
  'dif_uart_test',
  sources: [
    'dif_uart_test.cc',
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

test('dif_plic_test', executable(
  'dif_plic_test',
  sources: [
    hw_top_earlgrey_rv_plic_reg_h,
    meson.source_root() / 'sw/device/lib/dif/dif_plic.c',
    'dif_plic_test.cc',
  ],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  c_args: ['-DMOCK_MMIO'], 
  cpp_args: ['-DMOCK_MMIO'],
))