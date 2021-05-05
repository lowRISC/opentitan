# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Linker Parameters
#
# See sw/device/exts/common/flash_link.ld for additional info about these
# parameters.
rom_linkfile = files(['mask_rom.ld'])
rom_link_args = [
  '-Wl,-L,@0@'.format(meson.source_root()),
  '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_linkfile[0]),
  # Flatten the array, otherwise `mask_rom_lib` generation fails.
  ''.join(embedded_target_extra_link_args),
]
rom_link_deps = [rom_linkfile]

# MaskROM library.
mask_rom_lib = declare_dependency(
  sources: [
    'mask_rom_start.S',
  ],
    link_args: rom_link_args,
    dependencies: [
      freestanding_headers,
      sw_silicon_creator_lib_driver_hmac,
      sw_silicon_creator_lib_driver_uart,
      sw_silicon_creator_lib_fake_deps,
      rom_ext_manifest_parser,
      sw_lib_crt,
      sw_lib_pinmux,
      sw_lib_runtime_print,
    ],
    link_with: static_library(
      'mask_rom_lib',
      sources: [
        rom_exts_manifest_offsets_header,
        'mask_rom.c'
      ],
      link_depends: [rom_linkfile],
  )
)

# Production MaskROM images
foreach device_name, device_lib : sw_lib_arch_core_devices
  mask_rom_elf = executable(
    'mask_rom_' + device_name,
    name_suffix: 'elf',
    link_depends: rom_link_deps,
    link_args: [
      '-Wl,-Map=@0@/mask_rom_@1@.map'.format(meson.current_build_dir(), device_name),
    ],
    dependencies: [
      device_lib,
      mask_rom_lib,
    ],
  )

  mask_rom_embedded = custom_target(
    'mask_rom_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: mask_rom_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  mask_rom_scrambled = custom_target(
    'mask_rom_scrambled_' + device_name,
    command: scramble_image_command,
    depend_files: scramble_image_depend_files,
    input: mask_rom_elf,
    output: scramble_image_outputs,
    build_by_default: true,
  )

  custom_target(
    'mask_rom_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      mask_rom_elf,
      mask_rom_embedded,
      mask_rom_scrambled,
    ],
    output: 'mask_rom_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach

test('sw_silicon_creator_mask_rom_sig_verify_unittest', executable(
    'sw_silicon_creator_mask_rom_sig_verify_unittest',
    sources: [
      'sig_verify_unittest.cc',
      'sig_verify.c',
      'sig_verify_keys.c',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ), 
  suite: 'mask_rom',
)
