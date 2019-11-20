# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'hello_usbdev',
  command: make_embedded_target,
  output: make_embedded_target_outputs,
  input: executable(
    'hello_usbdev',
    sources: ['hello_usbdev.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_gpio,
      sw_lib_irq,
      sw_lib_uart,
      sw_lib_usb,
      riscv_crt,
    ],
  ),
)
