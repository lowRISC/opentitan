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
      meson.source_root() / 'util/rom_chip_info.py',
      '--outdir', '@OUTDIR@',
      '--ot_version', ot_version,
    ],
    depend_files: [
      meson.source_root() / 'util/rom_chip_info.py',
    ],
  )],
)

# ROM linker parameters.
#
# See sw/device/exts/common/flash_link.ld for additional info about these
# parameters.
rom_linkfile = files(['rom_link.ld'])
rom_link_args = [
  '-Wl,-L,@0@'.format(meson.source_root()),
  '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_linkfile[0]),
  '-Wl,--build-id=none',
]
rom_link_deps = [rom_linkfile]

foreach device_name, device_lib : sw_lib_arch_core_devices
  boot_rom_elf = executable(
    'boot_rom_' + device_name,
    sources: [
      'boot_rom.c',
      'bootstrap.c',
      'irq_vector.S',
      'rom_crt.S',
    ],
    name_suffix: 'elf',
    link_args: rom_link_args,
    link_depends: rom_link_deps,
    dependencies: [
      chip_info_h,
      sw_lib_crt,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_flash_ctrl,
      sw_lib_pinmux,
      sw_lib_dif_gpio,
      sw_lib_dif_spi_device,
      sw_lib_hmac,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
      top_earlgrey,
      device_lib,
      sw_lib_testing_test_status,
    ],
  )

  boot_rom_embedded = custom_target(
    'boot_rom_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: boot_rom_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  boot_rom_sim_dv_logs = []
  if device_name == 'sim_dv'
    boot_rom_sim_dv_logs = custom_target(
      'boot_rom_dv_logs',
      # Boot_rom has additional RO data sections of interest to DV logging.
      command: [
        extract_sw_logs_sim_dv_command,
        '--rodata-sections', '.chip_info',
      ],
      depend_files: [extract_sw_logs_sim_dv_depend_files,],
      input: boot_rom_elf,
      output: extract_sw_logs_sim_dv_outputs,
    )
  endif

  custom_target(
    'boot_rom_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [boot_rom_elf, boot_rom_embedded, boot_rom_sim_dv_logs,],
    output: 'boot_rom_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
