# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('lib')

# Dictionary for SCA programs.
sca_programs = {
  # 'program_name': {
  #   'dependency': dependency_name,
  # },
}

aes_serial = declare_dependency(
  sources: ['aes_serial.c'],
  dependencies: [
    sw_lib_dif_aes,
  ],
)
sca_programs += {
  'aes_serial': {
    'dependency': aes_serial,
  },
}

sha3_serial = declare_dependency(
  sources: [
    'sha3_serial.c',
    hw_ip_kmac_reg_h,
  ],
  dependencies: [
    sw_lib_dif_kmac,
  ],
)
sca_programs += {
  'sha3_serial': {
    'dependency': sha3_serial,
  },
}

foreach sca_program_name, sca_program_info: sca_programs
  foreach device_name, device_lib : sw_lib_arch_core_devices
    sca_program_elf = executable(
      '@0@_@1@'.format(sca_program_name, device_name),
      name_suffix: 'elf',
      dependencies: [
        device_lib,
        ottf_start_lib,
        sw_lib_mmio,
        sw_lib_runtime_hart,
        sw_lib_runtime_log,
        sw_sca_lib_prng,
        sw_sca_lib_sca,
        sw_sca_lib_simple_serial,
        sca_program_info['dependency'],
      ]
    )

    target_name = sca_program_name + '_@0@_' + device_name

    sca_program_dis = custom_target(
      target_name.format('dis'),
      input: sca_program_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    sca_program_bin = custom_target(
      target_name.format('bin'),
      input: sca_program_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    sca_program_vmem32 = custom_target(
      target_name.format('vmem32'),
      input: sca_program_bin,
      kwargs: bin_to_vmem32_custom_target_args,
    )

    sca_program_vmem64 = custom_target(
      target_name.format('vmem64'),
      input: sca_program_bin,
      kwargs: bin_to_vmem64_custom_target_args,
    )

    sca_program_scr_vmem64 = custom_target(
      target_name.format('scrambled'),
      input: sca_program_vmem64,
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
        sca_program_elf,
        sca_program_dis,
        sca_program_bin,
        sca_program_vmem32,
        sca_program_vmem64,
        sca_program_scr_vmem64,
      ],
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
