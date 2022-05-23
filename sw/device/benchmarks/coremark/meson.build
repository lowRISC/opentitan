# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  if device_name == 'fpga_cw310'
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
      device_lib,
      ottf_start_lib,
      sw_lib_dif_uart,
      sw_lib_mem,
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

  target_name = 'coremark_top_earlgrey_@0@_' + device_name

  coremark_top_earlgrey_dis = custom_target(
    target_name.format('dis'),
    input: coremark_top_earlgrey_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  coremark_top_earlgrey_bin = custom_target(
    target_name.format('bin'),
    input: coremark_top_earlgrey_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  coremark_top_earlgrey_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: coremark_top_earlgrey_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  coremark_top_earlgrey_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: coremark_top_earlgrey_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  coremark_top_earlgrey_scr_vmem64 = custom_target(
    target_name.format('scrambled'),
    input: coremark_top_earlgrey_vmem64,
    output: flash_image_outputs,
    command: flash_image_command,
    depend_files: flash_image_depend_files,
    build_by_default: true,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    input: [
      coremark_top_earlgrey_elf,
      coremark_top_earlgrey_dis,
      coremark_top_earlgrey_bin,
      coremark_top_earlgrey_vmem32,
      coremark_top_earlgrey_vmem64,
    ],
    depend_files: [export_target_depend_files,],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
