# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('lib')

foreach device_name, device_lib : sw_lib_arch_core_devices
  aes_serial_elf = executable(
    'aes_serial_' + device_name,
    sources: ['aes_serial.c'],
    name_suffix: 'elf',
    dependencies: [
      device_lib,
      riscv_crt,
      sw_lib_dif_aes,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_runtime_log,
      sw_sca_lib_prng,
      sw_sca_lib_sca,
      sw_sca_lib_simple_serial,
    ],
  )

  target_name = 'aes_serial_@0@_' + device_name

  aes_serial_dis = custom_target(
    target_name.format('dis'),
    input: aes_serial_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  aes_serial_bin = custom_target(
    target_name.format('bin'),
    input: aes_serial_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  aes_serial_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: aes_serial_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  aes_serial_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: aes_serial_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      aes_serial_elf,
      aes_serial_dis,
      aes_serial_bin,
      aes_serial_vmem32,
      aes_serial_vmem64,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
