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

# Signature verification.
sw_silicon_creator_mask_rom_sigverify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_mask_rom_sigverify',
    sources: [
      'sigverify_keys.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
    ],
  ),
)

# ROM_EXT image.
sw_silicon_creator_mask_rom_romextimage = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_mask_rom_romextimage',
    sources: [
      'romextimage.c',
    ],
  ),
)

# MaskROM library.
mask_rom_lib = declare_dependency(
  sources: [
    hw_ip_entropy_src_reg_h,
    hw_ip_csrng_reg_h,
    hw_ip_edn_reg_h,
    'mask_rom_start.S',
  ],
    link_args: rom_link_args,
    dependencies: [
      freestanding_headers,
      sw_silicon_creator_lib_driver_hmac,
      sw_silicon_creator_lib_driver_keymgr,
      sw_silicon_creator_lib_driver_uart,
      sw_silicon_creator_lib_fake_deps,
      sw_silicon_creator_lib_manifest,
      sw_silicon_creator_mask_rom_sigverify,
      sw_silicon_creator_mask_rom_romextimage,
      sw_lib_crt,
      sw_lib_pinmux,
      sw_lib_runtime_print,
    ],
    link_with: static_library(
      'mask_rom_lib',
      sources: [
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

test('sw_silicon_creator_mask_rom_romextimage_unittest', executable(
    'sw_silicon_creator_mask_rom_romextimage_unittest',
    sources: [
      'romextimage_unittest.cc',
      'romextimage.c',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

test('sw_silicon_creator_mask_rom_sigverify_keys_unittest', executable(
    'sw_silicon_creator_mask_rom_sigverify_keys_unittest',
    sources: [
      'sigverify_keys.c',
      'sigverify_keys_unittest.cc',
    ] + sw_silicon_creator_lib_sigverify_sources_for_boot_stage_tests,
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
  ),
  suite: 'mask_rom',
)
