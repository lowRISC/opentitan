# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
