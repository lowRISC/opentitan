# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  flash_test_elf = executable(
    'flash_test_' + device_name,
    sources: ['flash_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_runtime_hart,
      sw_lib_flash_ctrl,
      sw_lib_dif_gpio,
      sw_lib_irq,
      sw_lib_uart,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
    ],
  )

  flash_test_embedded = custom_target(
    'flash_test_' + device_name,
    command: make_embedded_target,
    input: flash_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'flash_test_export_' + device_name,
    command: export_embedded_target,
    input: [flash_test_elf, flash_test_embedded],
    output: 'flash_test_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
