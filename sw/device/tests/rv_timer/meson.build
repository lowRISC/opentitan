# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'rv_timer_test',
  command: make_embedded_target,
  output: make_embedded_target_outputs,
  input: executable(
    'rv_timer_test',
    sources: ['rv_timer_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_irq,
      sw_lib_rv_timer,
      sw_lib_uart,
      riscv_crt,
    ],
  ),
)
