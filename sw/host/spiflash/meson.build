# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

executable(
  'spiflash',
  [
    'ftdi_spi_interface.cc',
    'spiflash.cc',
    'updater.cc',
    'verilator_spi_interface.cc',
  ],
  dependencies: [
    dependency('libcrypto', native: true),
    libmpsse
  ],
  native: true,
)
