# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Linker Parameters
#
# See sw/device/exts/common/flash_link.ld for additional info about these
# parameters.
rom_ext_linkfile = files(['rom_ext.ld'])
rom_ext_link_args = [
  '-Wl,-L,@0@'.format(meson.source_root()),
  '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_ext_linkfile[0]),
  '-Wl,--build-id=none',
]
rom_ext_link_deps = [rom_ext_linkfile]

# ROM_EXT manifest generator.
rom_exts_manifest_offsets_header = custom_target(
  'rom_exts_manifest_h',
  output: 'manifest.h',
  depend_files: [
    'manifest.h.tpl',
    'manifest.hjson',
  ],
  command: [
    prog_python,
    meson.source_root() / 'util/rom-ext-manifest-generator.py',
    '--input-dir', meson.current_source_dir(),
    '--output-dir', meson.current_build_dir(),
  ],
)

# ROM_EXT manifest parser.
rom_ext_manifest_parser = declare_dependency(
  link_with: static_library(
    'rom_ext_manifest_parser',
    sources: [
      'rom_ext_manifest_parser.c',
      rom_exts_manifest_offsets_header,
    ],
    dependencies: [
      sw_lib_mmio,
    ],
  )
)

foreach device_name, device_lib : sw_lib_arch_core_devices
  rom_ext_elf = executable(
    'rom_ext_' + device_name,
    sources: [
      'rom_ext_manifest.S',
      'rom_ext_start.S',
      'rom_ext.c',
    ],
    name_suffix: 'elf',
    link_args: rom_ext_link_args,
    link_depends: rom_ext_link_deps,
    dependencies: [
      device_lib,
      sw_lib_dif_uart,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
    ],
  )

  rom_ext_embedded = custom_target(
    'rom_ext_' + device_name,
    command: make_embedded_target,
    input: rom_ext_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'rom_ext_export_' + device_name,
    command: export_embedded_target,
    input: [rom_ext_elf, rom_ext_embedded],
    output: 'rom_ext_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
