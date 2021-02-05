# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  hello_small_elf = executable(
    'hello_small_' + device_name,
    sources: ['hello_small.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_dif_uart,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib
    ],
  )

  hello_small_embedded = custom_target(
    'hello_small_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: hello_small_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'hello_small_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [hello_small_elf, hello_small_embedded],
    output: 'hello_small_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
