# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

rv_timer_test_elf = executable(
  'rv_timer_test',
  sources: ['rv_timer_test.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_irq,
    sw_lib_rv_timer,
    sw_lib_uart,
    riscv_crt,
    sw_lib_irq_handlers,
  ],
)

rv_timer_test_embedded = custom_target(
  'rv_timer_test',
  command: make_embedded_target,
  input: rv_timer_test_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'rv_timer_test_export',
  command: export_embedded_target,
  input: [rv_timer_test_elf, rv_timer_test_embedded],
  output: 'rv_timer_test',
  build_always_stale: true,
  build_by_default: true,
)
