# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  if device_name == 'fpga_nexysvideo'
    coremark_iterations = 100
  else
    coremark_iterations = 1
  endif

  coremark_top_earlgrey_elf = executable(
    'coremark_top_earlgrey_' + device_name,
    sources: [
      'top_earlgrey/core_portme.c',
      'top_earlgrey/ee_printf.c',
      vendor_coremark_base_files,
    ],
    name_suffix: 'elf',
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mem,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
      sw_lib_testing_test_status,
    ],
    # Set up coremark-specific defines.
    c_args: [
      '-Wno-implicit-fallthrough',
      '-Wno-strict-prototypes',
      '-DITERATIONS=@0@'.format(coremark_iterations),
      '-DPERFORMANCE_RUN=1',
      '-DTOTAL_DATA_SIZE=2000',
      '-DMAIN_HAS_NOARGC=1',
    ],
  )

  coremark_top_earlgrey_embedded = custom_target(
    'coremark_top_earlgrey_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: coremark_top_earlgrey_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'coremark_top_earlgrey_export_' + device_name,
    command: export_target_command,
    input: [
      coremark_top_earlgrey_elf,
      coremark_top_earlgrey_embedded,
    ],
    depend_files: [export_target_depend_files,],
    output: 'coremark_top_earlgrey_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
