# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_examples_demos = declare_dependency(
  link_with: static_library(
    'sw_examples_demos',
    sources: ['demos.c'],
    dependencies: [
      sw_lib_runtime_hart,
      sw_lib_dif_gpio,
      sw_lib_dif_spi_device,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
    ],
  )
)

subdir('hello_usbdev')
subdir('hello_world')
