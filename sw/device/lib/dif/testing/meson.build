# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_dif_testing_mock_mmio = declare_dependency(
  link_with: static_library(
    'sw_dif_testing_mock_mmio',
    sources: [
      'mock_mmio.cc',
      'mmio_externs.c',
    ],
    native: true,
  ),
)

sw_dif_testing_fixture = declare_dependency(
  link_with: static_library(
    'sw_dif_testing_fixture',
    sources: ['fixture.cc'],
    c_args: ['-DMOCK_MMIO'],
    native: true,
  ),
)
