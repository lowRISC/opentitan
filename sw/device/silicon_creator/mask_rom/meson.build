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
] + embedded_target_extra_link_args
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

  target_name = 'mask_rom_@0@_' + device_name

  mask_rom_dis = custom_target(
    target_name.format('dis'),
    input: mask_rom_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  mask_rom_bin = custom_target(
    target_name.format('bin'),
    input: mask_rom_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  mask_rom_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: mask_rom_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  mask_rom_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: mask_rom_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  mask_rom_scrambled = custom_target(
    target_name.format('scrambled'),
    command: scramble_image_command,
    depend_files: scramble_image_depend_files,
    input: mask_rom_elf,
    output: scramble_image_outputs,
    build_by_default: true,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      mask_rom_elf,
      mask_rom_dis,
      mask_rom_bin,
      mask_rom_vmem32,
      mask_rom_vmem64,
      mask_rom_scrambled,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach

test('sw_silicon_creator_mask_rom_rsa_verify_unittest', executable(
    'sw_silicon_creator_mask_rom_rsa_verify_unittest',
    sources: [
      'rsa_verify.c',
      'sig_verify_keys.c',
      'rsa_verify_unittest.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)

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
