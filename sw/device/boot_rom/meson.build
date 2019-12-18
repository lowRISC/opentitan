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
      '@SOURCE_DIR@/util/rom_chip_info.py',
      '--outdir', '@OUTDIR@',
      '--ot_version', ot_version,
    ]
  )],
)

# ROM linker parameters.
rom_linkfile = files(['rom_link.ld'])
rom_link_args = ['-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_linkfile[0]), '-Wl,--build-id=none']
rom_link_deps = [rom_linkfile]

boot_rom_elf = executable(
  'boot_rom',
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
    sw_lib_runtime_hart,
    sw_lib_flash_ctrl,
    sw_lib_pinmux,
    sw_lib_gpio,
    sw_lib_hmac,
    sw_lib_spi_device,
    sw_lib_uart,
    sw_lib_log,
  ],
)

boot_rom_embedded = custom_target(
  'boot_rom',
  command: make_embedded_target,
  input: boot_rom_elf,
  output: make_embedded_target_outputs,
  build_by_default: true,
)

custom_target(
  'boot_rom_export',
  command: export_embedded_target,
  input: [boot_rom_elf, boot_rom_embedded],
  output: 'boot_rom_export',
  build_always_stale: true,
  build_by_default: true,
)

