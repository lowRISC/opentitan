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
    dependencies: [sw_lib_runtime_ibex],
  )
)
