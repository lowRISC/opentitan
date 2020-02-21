# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  rv_timer_test_elf = executable(
    'rv_timer_test_' + device_name,
    sources: ['rv_timer_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_irq,
      sw_lib_rv_timer,
      sw_lib_uart,
      sw_lib_dif_gpio,
      sw_lib_pinmux,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
    ],
  )

  rv_timer_test_embedded = custom_target(
    'rv_timer_test_' + device_name,
    command: make_embedded_target,
    input: rv_timer_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'rv_timer_test_export_' + device_name,
    command: export_embedded_target,
    input: [rv_timer_test_elf, rv_timer_test_embedded],
    output: 'rv_timer_test_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
