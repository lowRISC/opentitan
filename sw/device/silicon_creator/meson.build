# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is defined here so it is visible in all child subdirectories.
mask_rom_tests = {
  # 'test_name': {
  #   'library': test_lib,
  #   'dv_frames': true/false, # (can be omitted, defaults to `false`)
  # },
}

foreach sw_test_name, sw_test_info : mask_rom_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    sw_test_elf = executable(
      sw_test_name + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        riscv_crt,
        device_lib,
        sw_test_info['library'],
        sw_lib_irq_handlers,
        sw_lib_testing_test_main,
      ],
    )

    target_name = sw_test_name + '_@0@_' + device_name

    sw_test_dis = custom_target(
      target_name.format('dis'),
      input: sw_test_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    sw_test_bin = custom_target(
      target_name.format('bin'),
      input: sw_test_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    sw_test_vmem32 = custom_target(
      target_name.format('vmem32'),
      input: sw_test_bin,
      kwargs: bin_to_vmem32_custom_target_args,
    )

    sw_test_vmem64 = custom_target(
      target_name.format('vmem64'),
      input: sw_test_bin,
      kwargs: bin_to_vmem64_custom_target_args,
    )

    sw_test_sim_dv_frames = []
    if device_name == 'sim_dv' and \
        sw_test_info.has_key('dv_frames') and sw_test_info['dv_frames']
      sw_test_sim_dv_frames_bin = custom_target(
        sw_test_name + '_sim_dv_frames_bin',
        command: [
          spiflash_bin,
          '--input=@INPUT@',
          '--dump-frames=@OUTPUT@',
        ],
        input: sw_test_bin,
        output: '@BASENAME@.frames.bin',
      )

      sw_test_sim_dv_frames_vmem = custom_target(
        sw_test_name + '_sim_dv_frames_vmem',
        command: [
          prog_srec_cat,
          '@INPUT@',
          '--binary',
          '--offset', '0x0',
          '--byte-swap', '4',
          '--fill', '0xff',
          '-within', '@INPUT@',
          '-binary',
          '-range-pad', '4',
          '--output', '@OUTPUT@',
          '--vmem',
        ],
        input: sw_test_sim_dv_frames_bin,
        output: '@BASENAME@.vmem',
      )
      sw_test_sim_dv_frames = [
        sw_test_sim_dv_frames_bin,
        sw_test_sim_dv_frames_vmem,
      ]
    endif

    sw_test_sim_dv_logs = []
    if device_name == 'sim_dv'
      sw_test_sim_dv_logs = custom_target(
        sw_test_name + '_sim_dv_logs',
        command: extract_sw_logs_sim_dv_command,
        depend_files: [extract_sw_logs_sim_dv_depend_files,],
        input: sw_test_elf,
        output: extract_sw_logs_sim_dv_outputs,
      )
    endif

    custom_target(
      target_name.format('export'),
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: [
        sw_test_elf,
        sw_test_dis,
        sw_test_bin,
        sw_test_vmem32,
        sw_test_vmem64,
        sw_test_sim_dv_frames,
        sw_test_sim_dv_logs,
      ],
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach


subdir('lib')
subdir('rom_exts')
subdir('mask_rom')
subdir('testing')
