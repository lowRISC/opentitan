# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Linker Parameters
#
# See sw/device/exts/common/flash_link.ld for additional info about these
# parameters.

rom_ext_linkfile_slot_a = files(['rom_ext_slot_a.ld'])
rom_ext_linkfile_slot_b = files(['rom_ext_slot_b.ld'])

rom_ext_link_info = {
  'rom_ext_slot_a' :
  [
    # Link arguments for slot A.
    [
      '-Wl,-L,@0@'.format(meson.source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_ext_linkfile_slot_a[0]),
      embedded_target_extra_link_args,
    ],
    # Link dependency file for slot A.
    [
      rom_ext_linkfile_slot_a,
    ],
  ],
  'rom_ext_slot_b' :
  [
    # Link arguments for slot B.
    [
      '-Wl,-L,@0@'.format(meson.source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_ext_linkfile_slot_b[0]),
      embedded_target_extra_link_args,
    ],
    # Link dependency file for slot B.
    [
      rom_ext_linkfile_slot_b,
    ],
  ],
}

# ROM_EXT manifest generator.
rom_exts_manifest_offsets_header = custom_target(
  'rom_exts_manifest_h',
  output: 'manifest.h',
  depend_files: [
    'manifest.h.tpl',
    'manifest.hjson',
    meson.source_root() / 'util/rom-ext-manifest-generator.py',
  ],
  command: [
    prog_python,
    meson.source_root() / 'util/rom-ext-manifest-generator.py',
    '--input-dir', meson.current_source_dir(),
    '--output-dir', meson.current_build_dir(),
    '--output-files', 'c',
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
  ),
  sources: [
    rom_exts_manifest_offsets_header,
  ],
)

foreach device_name, device_lib : sw_lib_arch_core_devices
  foreach slot, slot_link_args : rom_ext_link_info
    rom_ext_elf = executable(
      slot + '_' + device_name,
      sources: [
        'rom_ext_manifest.S',
        'rom_ext_start.S',
        'rom_ext.c',
      ],
      name_suffix: 'elf',
      link_args: slot_link_args[0],
      link_depends: slot_link_args[1],
      dependencies: [
        device_lib,
        sw_lib_crt,
        sw_lib_dif_uart,
        sw_lib_runtime_hart,
        sw_lib_runtime_print,
      ],
    )

    rom_ext_embedded = custom_target(
      slot + '_' + device_name,
      command: make_embedded_target_command,
      depend_files: [make_embedded_target_depend_files,],
      input: rom_ext_elf,
      output: make_embedded_target_outputs,
      build_by_default: true,
    )

    custom_target(
      slot + '_export_' + device_name,
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: [rom_ext_elf, rom_ext_embedded],
      output: slot + '_export_' + device_name,
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
