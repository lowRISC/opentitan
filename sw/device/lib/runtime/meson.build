# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_runtime_ibex = declare_dependency(
  link_with: static_library(
    'runtime_ibex_ot',
    sources: ['ibex.c'],
  )
)

sw_lib_runtime_hart = declare_dependency(
  link_with: static_library(
    'runtime_hart_ot',
    sources: ['hart.c'],
    dependencies: [
      sw_lib_runtime_ibex,
      sw_lib_mmio,
    ],
  )
)

sw_lib_runtime_pmp = declare_dependency(
  link_with: static_library(
    'runtime_pmp_ot',
    sources: ['pmp.c'],
    dependencies: [
      sw_lib_bitfield,
    ],
  )
)

sw_lib_runtime_print = declare_dependency(
  link_with: static_library(
    'runtime_print_ot',
    sources: ['print.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_dif_uart,
    ],
  )
)

sw_lib_runtime_log = declare_dependency(
  link_with: static_library(
    'runtime_log_ot',
    sources: ['log.c'],
    dependencies: [
      sw_lib_runtime_print,
    ],
  )
)

sw_lib_runtime_otbn = declare_dependency(
  link_with: static_library(
    'otbn_ot',
    sources: [
      'otbn.c',
    ],
    dependencies: [
      sw_lib_dif_otbn,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ]
  )
)
