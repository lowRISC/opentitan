# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'hello_world',  
  command: make_embedded_target,
  output: make_embedded_target_outputs,
  input: executable(
    'hello_world',
    sources: ['hello_world.c',],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_pinmux,
      sw_lib_gpio,
      sw_lib_irq,
      sw_lib_spi_device,
      sw_lib_uart,
      riscv_crt,
    ],
  ),
)
