# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  hello_world_elf = executable(
    'hello_world_' + device_name,
    sources: ['hello_world.c'],
    name_suffix: 'elf',
    dependencies: [
      device_lib,
      ottf_start_lib,
      sw_examples_demos,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_pinmux,
      sw_lib_dif_gpio,
      sw_lib_irq,
      sw_lib_dif_spi_device,
      sw_lib_dif_uart,
      sw_lib_testing_test_status,
    ],
  )

  target_name = 'hello_world_@0@_' + device_name

  hello_world_dis = custom_target(
    target_name.format('dis'),
    input: hello_world_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  hello_world_bin = custom_target(
    target_name.format('bin'),
    input: hello_world_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  hello_world_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: hello_world_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  hello_world_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: hello_world_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  hello_world_scr_vmem64 = custom_target(
    target_name.format('scrambled'),
    input: hello_world_vmem64,
    output: flash_image_outputs,
    command: flash_image_command,
    depend_files: flash_image_depend_files,
    build_by_default: true,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      hello_world_elf,
      hello_world_dis,
      hello_world_bin,
      hello_world_vmem32,
      hello_world_vmem64,
      hello_world_scr_vmem64,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
