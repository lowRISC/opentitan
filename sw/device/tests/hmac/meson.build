# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

custom_target(
  'sha256_test',
  command: make_embedded_target,
  output: make_embedded_target_outputs,
  input: executable(
    'sha256_test',
    sources: ['sha256_test.c'],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_flash_ctrl,
      sw_lib_hmac,
      sw_lib_irq,
      sw_lib_uart,
      riscv_crt,
    ],
  ),
)
