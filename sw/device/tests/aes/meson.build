# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  aes_test_elf = executable(
    'aes_test_' + device_name,
    sources: ['aes_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_aes,
      sw_lib_uart,
      sw_lib_mem,
      riscv_crt,
      device_lib,
    ],
  )

  aes_test_embedded = custom_target(
    'aes_test_' + device_name,
    command: make_embedded_target,
    input: aes_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'aes_test_export_' + device_name,
    command: export_embedded_target,
    input: [aes_test_elf, aes_test_embedded],
    output: 'aes_test_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
