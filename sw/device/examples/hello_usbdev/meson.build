# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

hello_usbdev_elf = executable(
  'hello_usbdev',
  sources: ['hello_usbdev.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_runtime_hart,
    sw_lib_gpio,
    sw_lib_irq,
    sw_lib_uart,
    sw_lib_usb,
    riscv_crt,
    sw_lib_irq_handlers,
  ],
)

hello_usbdev_embedded = custom_target(
  'hello_usbdev',
  command: make_embedded_target,
  input: hello_usbdev_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'hello_usbdev_export',
  command: export_embedded_target,
  input: [hello_usbdev_elf, hello_usbdev_embedded],
  output: 'hello_usbdev_export',
  build_always_stale: true,
  build_by_default: true,
)
