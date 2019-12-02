# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if target == 'sim-verilator'
  coremark_iterations = 1
else
  coremark_iterations = 100
endif

coremark_top_earlgrey_elf = executable(
  'coremark_top_earlgrey',
  sources: [
    'top_earlgrey/core_portme.c',
    'top_earlgrey/ee_printf.c',
    vendor_coremark_base_files,
  ],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_uart,
    sw_lib_mem,
    riscv_crt,
  ],
  # Set up coremark-specific defines.
  c_args: [
    '-DITERATIONS=@0@'.format(coremark_iterations),
    '-DPERFORMANCE_RUN=1',
    '-DTOTAL_DATA_SIZE=2000',
    '-DMAIN_HAS_NOARGC=1',
  ],
)

coremark_top_earlgrey_embedded = custom_target(
  'coremark_top_earlgrey',
  command: make_embedded_target,
  input: coremark_top_earlgrey_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'coremark_top_earlgrey_export',
  command: export_embedded_target,
  input: [
    coremark_top_earlgrey_elf,
    coremark_top_earlgrey_embedded,
  ],
  output: 'coremark_top_earlgrey_export',
  build_always_stale: true,
  build_by_default: true,
)
