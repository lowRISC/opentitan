# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

aes_test_elf = executable(
  'aes_test',
  sources: ['aes_test.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_aes,
    sw_lib_uart,
    sw_lib_mem,
    riscv_crt,
  ],
)

aes_test_embedded = custom_target(
  'aes_test',
  command: make_embedded_target,
  input: aes_test_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'aes_test_export',
  command: export_embedded_target,
  input: [aes_test_elf, aes_test_embedded],
  output: 'aes_test',
  build_always_stale: true,
  build_by_default: true,
)
