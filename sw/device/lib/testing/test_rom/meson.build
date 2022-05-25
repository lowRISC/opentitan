# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Generate header file with chip_info information.
chip_info_h = declare_dependency(
  sources: [custom_target(
    'chip_info_h',
    output: 'chip_info.h',
    command: [
      prog_python,
      meson.project_source_root() / 'util/rom_chip_info.py',
      '--outdir', '@OUTDIR@',
      '--ot_version', ot_version,
    ],
    depend_files: [
      meson.project_source_root() / 'util/rom_chip_info.py',
    ],
  )],
)

# Test ROM linker parameters.
#
# See `sw/device/lib/testing/test_framework/ottf.ld` for additional info
# about these parameters.
test_rom_linker_script = '@0@/@1@'.format(meson.project_source_root(), files(['test_rom.ld'])[0])
test_rom_link_args = [
  '-Wl,-L,@0@'.format(meson.project_source_root()),
  '-Wl,-T,@0@'.format(test_rom_linker_script),
  '-Wl,--build-id=none',
]
test_rom_link_deps = [test_rom_linker_script]

foreach device_name, device_lib : sw_lib_arch_core_devices
  test_rom_elf = executable(
    'test_rom_' + device_name,
    sources: [
      hw_ip_ast_reg_h,
      hw_ip_clkmgr_reg_h,
      hw_ip_csrng_reg_h,
      hw_ip_edn_reg_h,
      hw_ip_entropy_src_reg_h,
      hw_ip_otp_ctrl_reg_h,
      hw_ip_sram_ctrl_reg_h,
      hw_ip_sensor_ctrl_reg_h,
      hw_ip_flash_ctrl_reg_h,
      hw_ip_lc_ctrl_reg_h,
      hw_ip_rstmgr_reg_h,
      hw_ip_gpio_reg_h,
      hw_ip_spi_device_reg_h,
      'test_rom.c',
      'test_rom_start.S',
      meson.project_source_root() / 'sw/device/silicon_creator/mask_rom/bootstrap.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/drivers/spi_device.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/drivers/flash_ctrl.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/drivers/lifecycle.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/drivers/otp.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/drivers/rstmgr.c',
      meson.project_source_root() / 'sw/device/silicon_creator/lib/base/sec_mmio.c',
    ],
    name_suffix: 'elf',
    link_args: test_rom_link_args,
    link_depends: test_rom_link_deps,
    dependencies: [
      chip_info_h,
      sw_lib_crt,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_ibex,
      sw_lib_dif_clkmgr,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_gpio,
      sw_lib_dif_spi_device,
      sw_lib_dif_hmac,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
      sw_lib_testing_flash_ctrl_testutils,
      sw_lib_testing_pinmux_testutils,
      top_earlgrey,
      device_lib,
      sw_lib_testing_test_status,
    ],
  )

  target_name = 'test_rom_@0@_' + device_name

  test_rom_dis = custom_target(
    target_name.format('dis'),
    input: test_rom_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  test_rom_bin = custom_target(
    target_name.format('bin'),
    input: test_rom_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  test_rom_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: test_rom_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  test_rom_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: test_rom_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  test_rom_scrambled = custom_target(
    target_name.format('scrambled'),
    command: scramble_image_command,
    env: {'PYTHONPATH': meson.project_source_root()},
    depend_files: scramble_image_depend_files,
    input: test_rom_elf,
    output: scramble_image_outputs,
    build_by_default: true,
  )

  test_rom_sim_dv_logs = []
  if device_name == 'sim_dv'
    test_rom_sim_dv_logs = custom_target(
      'test_rom_dv_logs',
      # test_rom has additional RO data sections of interest to DV logging.
      command: [
        extract_sw_logs_sim_dv_command,
        '--rodata-sections', '.chip_info',
      ],
      depend_files: [extract_sw_logs_sim_dv_depend_files,],
      input: test_rom_elf,
      output: extract_sw_logs_sim_dv_outputs,
    )
  endif

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      test_rom_elf,
      test_rom_dis,
      test_rom_bin,
      test_rom_vmem32,
      test_rom_vmem64,
      test_rom_scrambled,
      test_rom_sim_dv_logs,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
