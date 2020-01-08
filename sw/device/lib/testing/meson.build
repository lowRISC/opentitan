# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_testing_gtest = declare_dependency(
  include_directories: include_directories(
    '/tools/googletest/gtest',
    '/tools/googletest/gmock',
  ),
  link_args: [
    '-L/tools/googletest/lib',
    '-lgtest',
    '-lgtest_main',
    '-lgmock',
    '-lpthread',
  ],
)

sw_lib_testing_mock_mmio = declare_dependency(
  link_with: static_library(
    'mock_mmio',
    sources: ['mock_mmio.cc'],
    dependencies: [sw_lib_testing_gtest],
    native: true,
    cpp_args: ['-DMOCK_MMIO'],
  )
)

dif_gpio_test = executable(
  'dif_gpio_test',
  sources: [
    hw_ip_gpio_reg_h,
    'dif_gpio_test.cc',
    meson.source_root() / 'sw/device/lib/dif/dif_gpio.c',
    meson.source_root() / 'sw/device/lib/base/mmio.c',
  ],
  dependencies: [
    sw_lib_testing_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  cpp_args: ['-DMOCK_MMIO'],
  c_args: ['-DMOCK_MMIO']
)

test('dif_gpio_test', dif_gpio_test)
