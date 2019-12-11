# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sha256_test_elf = executable(
  'sha256_test',
  sources: ['sha256_test.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_flash_ctrl,
    sw_lib_hmac,
    sw_lib_irq,
    sw_lib_uart,
    riscv_crt,
    sw_lib_irq_handlers,
  ],
)

sha256_test_embedded = custom_target(
  'sha256_test',
  command: make_embedded_target,
  input: sha256_test_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'sha256_test_export',
  command: export_embedded_target,
  input: [sha256_test_elf, sha256_test_embedded],
  output: 'sha256_test',
  build_always_stale: true,
  build_by_default: true,
)

