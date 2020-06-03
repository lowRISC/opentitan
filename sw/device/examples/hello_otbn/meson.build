# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  hello_otbn_elf = executable(
    'hello_otbn_' + device_name,
    sources: [
      'hello_otbn.c',
    ],
    name_suffix: 'elf',
    dependencies: [
      sw_examples_demos,
      sw_lib_runtime_hart,
      sw_lib_base_print,
      sw_lib_base_log,
      sw_lib_irq,
      sw_lib_uart,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
      sw_lib_testing_test_status,
      sw_lib_dif_otbn,
    ],
  )

  hello_otbn_embedded = custom_target(
    'hello_otbn_' + device_name,
    command: make_embedded_target,
    input: hello_otbn_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'hello_otbn_export_' + device_name,
    command: export_embedded_target,
    input: [hello_otbn_elf, hello_otbn_embedded],
    output: 'hello_otbn_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
