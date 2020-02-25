# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  consecutive_irqs_test_elf = executable(
    'consecutive_irqs_test_' + device_name,
    sources: ['consecutive_irqs_test.c'],
    name_suffix: 'elf',
    dependencies: [
      device_lib,
      dif_uart,
      dif_plic,
      riscv_crt,
      sw_lib_base_log,
      sw_lib_base_print,
      sw_lib_irq_handlers,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_uart,
    ],
  )

  consecutive_irqs_test_embedded = custom_target(
    'consecutive_irqs_test_' + device_name,
    command: make_embedded_target,
    input: consecutive_irqs_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'consecutive_irqs_test_export_' + device_name,
    command: export_embedded_target,
    input: [consecutive_irqs_test_elf, consecutive_irqs_test_embedded],
    output: 'consecutive_irqs_test_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
