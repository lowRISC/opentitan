# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('testing')

# SPI device DIF library
sw_dif_spi_device = declare_dependency(
  link_with: static_library(
    'sw_dif_spi_device',
    sources: [
      hw_ip_spi_device_reg_h,
      'dif_spi_device.c',
    ],
    dependencies: [sw_lib_mmio],
  )
)

test(
  'sw_dif_spi_device_test_test',
  executable(
    'sw_dif_spi_device_test',
    sources: [
      hw_ip_spi_device_reg_h,
      'dif_spi_device.c',
      'dif_spi_device_test.cc',
    ],
    dependencies: [
      sw_dif_testing_fixture,
      sw_dif_testing_mock_mmio,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO=1'],
    cpp_args: ['-DMOCK_MMIO=1'],
  )
)
