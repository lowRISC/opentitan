# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'hello_world',
  output: embedded_target_output,
  input: executable(
    'hello_world',
    ['hello_world.c', startup_files],
    name_suffix: 'elf',
    link_args: riscv_link_args,
    link_depends: riscv_link_deps,
    dependencies: [
      sw_lib_pinmux,
      sw_lib_gpio,
      sw_lib_irq,
      sw_lib_spi_device,
      sw_lib_uart,
    ],
  ),
  command: embedded_target_args,
  build_by_default: true,
)
