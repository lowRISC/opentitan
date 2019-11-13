# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Generate header file with chip_info information.
chip_info_h = custom_target(
  'chip_info_h',
  output: 'chip_info.h',
  command: [
    prog_python, '@SOURCE_DIR@/util/rom_chip_info.py', '--outdir', '@OUTDIR@']
)

# ROM linker parameters.
rom_linkfile = files(['rom_link.ld'])
rom_link_args = ['-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_linkfile[0])]
rom_link_deps = [rom_linkfile]

custom_target(
  'boot_rom',
  output: embedded_target_output,
  input: executable(
    'boot_rom',
    [
      chip_info_h,
      'boot_rom.c',
      'bootstrap.c',
      'crt0.S'
    ],
    name_suffix: 'elf',
    link_args: rom_link_args,
    link_depends: rom_link_deps,
    dependencies: [
      sw_lib_flash_ctrl,
      sw_lib_pinmux,
      sw_lib_gpio,
      sw_lib_hmac,
      sw_lib_spi_device,
      sw_lib_uart,
      sw_lib_log,
    ],
  ),
  command: embedded_target_args,
  build_by_default: true,
)
