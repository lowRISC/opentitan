# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

aes_hmac_demo_elf = executable(
  'aes_hmac_demo',
  sources: ['aes_hmac_demo.c'],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_aes,
    sw_lib_hmac,
    sw_lib_uart,
    riscv_crt,
  ],
)

aes_hmac_demo_embedded = custom_target(
  'aes_hmac_demo',
  command: make_embedded_target,
  input: aes_hmac_demo_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'aes_hmac_demo_export',
  command: export_embedded_target,
  input: [aes_hmac_demo_elf, aes_hmac_demo_embedded],
  output: 'aes_hmac_demo',
  build_always_stale: true,
  build_by_default: true,
)
