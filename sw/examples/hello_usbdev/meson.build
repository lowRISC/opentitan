# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'hello_usbdev',
  output: embedded_target_output,
  input: executable(
    'hello_usbdev',
    ['hello_usbdev.c', startup_files],
    name_suffix: 'elf',
    link_args: riscv_link_args,
    link_depends: riscv_link_deps,
    dependencies: [
      sw_lib_gpio,
      sw_lib_irq,
      sw_lib_uart,
      sw_lib_usb,
    ],
  ),
  command: embedded_target_args,
  build_by_default: true,
)
