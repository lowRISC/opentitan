# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  sha256_test_elf = executable(
    'sha256_test_' + device_name,
    sources: ['sha256_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_flash_ctrl,
      sw_lib_hmac,
      sw_lib_irq,
      sw_lib_uart,
      sw_lib_base_print,
      sw_lib_base_log,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
    ],
  )

  sha256_test_embedded = custom_target(
    'sha256_test_' + device_name,
    command: make_embedded_target,
    input: sha256_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'sha256_test_export_' + device_name,
    command: export_embedded_target,
    input: [sha256_test_elf, sha256_test_embedded],
    output: 'sha256_test_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
