# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_sca_lib_sca  = declare_dependency(
  link_with: static_library(
    'lib_sca',
    sources: ['sca.c'],
    dependencies: [
      sw_lib_dif_gpio,
      sw_lib_dif_rv_timer,
      sw_lib_dif_uart,
      sw_lib_irq,
      sw_lib_irq_handlers,
      sw_lib_mmio,
      sw_lib_pinmux,
      sw_lib_runtime_log,
    ],
  ),
)

sw_sca_lib_prng = declare_dependency(
  link_with: static_library(
    'lib_prng',
    sources: ['prng.c'],
  ),
)

sw_sca_lib_simple_serial = declare_dependency(
  link_with: static_library(
    'lib_simple_serial',
    sources: ['simple_serial.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_print,
      sw_sca_lib_prng,
    ]
  ),
)
