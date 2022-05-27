# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All tests added to this dictionary will result in build targets that have
# names starting `sw/device/silicon_creator/tests/<test_name>`. They will not
# contain the subdirectory name, because the build targets are really declared
# at the bottom of this file, rather than in the subdirectories.
## mask_rom_tests = {
##   # 'test_name': {
##   #   'library': test_lib,
##   #   'dv_frames': true/false, # (can be omitted, defaults to `false`)
##   # },
## }

foreach mask_rom_test_name, mask_rom_test_info : mask_rom_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    mask_rom_test_elf = executable(
      mask_rom_test_name + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        device_lib,
        mask_rom_test_info['library'],
        ottf_lib,
      ],
    )

    target_name = mask_rom_test_name + '_@0@_' + device_name

    mask_rom_test_dis = custom_target(
      target_name.format('dis'),
      input: mask_rom_test_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    mask_rom_test_bin = custom_target(
      target_name.format('bin'),
      input: mask_rom_test_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    mask_rom_test_vmem32 = custom_target(
      target_name.format('vmem32'),
      input: mask_rom_test_bin,
      kwargs: bin_to_vmem32_custom_target_args,
    )

    mask_rom_test_vmem64 = custom_target(
      target_name.format('vmem64'),
      input: mask_rom_test_bin,
      kwargs: bin_to_vmem64_custom_target_args,
    )

    mask_rom_test_scr_vmem64 = custom_target(
      target_name.format('scrambled'),
      input: mask_rom_test_vmem64,
      output: flash_image_outputs,
      command: flash_image_command,
      depend_files: flash_image_depend_files,
      build_by_default: true,
    )

    mask_rom_test_sim_dv_logs = []
    if device_name == 'sim_dv'
      mask_rom_test_sim_dv_logs = custom_target(
        mask_rom_test_name + '_sim_dv_logs',
        command: extract_sw_logs_sim_dv_command,
        depend_files: [extract_sw_logs_sim_dv_depend_files,],
        input: mask_rom_test_elf,
        output: extract_sw_logs_sim_dv_outputs,
      )
    endif

    custom_target(
      target_name.format('export'),
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: [
        mask_rom_test_elf,
        mask_rom_test_dis,
        mask_rom_test_bin,
        mask_rom_test_vmem32,
        mask_rom_test_vmem64,
        mask_rom_test_scr_vmem64,
        mask_rom_test_sim_dv_logs,
      ],
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
