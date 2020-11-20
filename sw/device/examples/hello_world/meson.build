# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  hello_world_elf = executable(
    'hello_world_' + device_name,
    sources: ['hello_world.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_examples_demos,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_pinmux,
      sw_lib_dif_gpio,
      sw_lib_irq,
      sw_lib_dif_spi_device,
      sw_lib_dif_uart,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
      sw_lib_testing_test_status,
    ],
  )

  hello_world_embedded = custom_target(
    'hello_world_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: hello_world_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'hello_world_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [hello_world_elf, hello_world_embedded],
    output: 'hello_world_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
