# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if target == 'sim-verilator'
  iterations = '-DITERATIONS=1'
else
  iterations = '-DITERATIONS=650'
endif

coremark_elf = executable(
  'coremark',
  sources: ['./top_earlgrey/core_portme.c',
            './top_earlgrey/ee_printf.c',
            coremark_base_files],
  name_suffix: 'elf',
  dependencies: [
    sw_lib_uart,
    sw_lib_mem,
    sw_lib_oled_display,
    riscv_crt,
  ],
  c_args : ['-DPERFORMANCE_RUN=1', iterations, '-DTOTAL_DATA_SIZE=2000', '-DMAIN_HAS_NOARGC=1', '-DOLED_DRIVER_INC_FONT']
)

coremark_embedded = custom_target(
  'coremark',
  command: make_embedded_target,
  input: coremark_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'coremark_export',
  command: export_embedded_target,
  input: [coremark_elf, coremark_embedded],
  output: 'coremark_export',
  build_always_stale: true,
  build_by_default: true,
)
