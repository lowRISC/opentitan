# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

hello_world_elf = executable(
  'hello_world',
  sources: ['hello_world.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_runtime_hart,
    sw_lib_pinmux,
    sw_lib_gpio,
    sw_lib_irq,
    sw_lib_spi_device,
    sw_lib_uart,
    riscv_crt,
    sw_lib_irq_handlers,
  ],
)

hello_world_embedded = custom_target(
  'hello_world',
  command: make_embedded_target,
  input: hello_world_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'hello_world_export',
  command: export_embedded_target,
  input: [hello_world_elf, hello_world_embedded],
  output: 'hello_world_export',
  build_always_stale: true,
  build_by_default: true,
)
