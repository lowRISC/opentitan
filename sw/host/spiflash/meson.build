# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

spiflash_bin = executable(
  'spiflash',
  sources: [
    'ftdi_spi_interface.cc',
    'spiflash.cc',
    'updater.cc',
    'verilator_spi_interface.cc',
  ],
  implicit_include_directories: false,
  dependencies: [
    dependency('libcrypto', native: true),
    libmpsse
  ],
  native: true,
)

custom_target(
  'spiflash_export',
  output: 'spiflash_export',
  command: export_target_command,
  depend_files: [export_target_depend_files,],
  input: spiflash_bin,
  build_always_stale: true,
  build_by_default: true,
)
