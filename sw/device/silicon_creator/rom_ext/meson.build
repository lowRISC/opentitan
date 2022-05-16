# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# ROM_EXT ePMP library
sw_silicon_creator_rom_ext_epmp = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_rom_ext_epmp',
    sources: [
      'rom_ext_epmp.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_epmp,
    ],
  )
)

# ROM_EXT boot policy.
sw_silicon_creator_rom_ext_boot_policy = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_rom_ext_boot_policy',
    sources: [
      'rom_ext_boot_policy.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_manifest,
    ],
  ),
)

test('sw_silicon_creator_rom_ext_boot_policy_unittest', executable(
    'sw_silicon_creator_rom_ext_boot_policy_unittest',
    sources: [
      'rom_ext_boot_policy_unittest.cc',
      'rom_ext_boot_policy.c',
    ],
    dependencies: [
      sw_vendor_gtest,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'rom_ext',
)

# Mask ROM Linker Parameters
#
# See `sw/device/lib/testing/test_framework/ottf.ld` for additional info
# about these parameters.

rom_ext_linkfile_slot_a = files(['rom_ext_slot_a.ld'])
rom_ext_linkfile_slot_b = files(['rom_ext_slot_b.ld'])
rom_ext_linkfile_virtual_addr = files(['rom_ext_virtual_addr.ld'])

rom_ext_link_info = {
  'rom_ext_slot_a' :
  [
    # Link arguments for slot A.
    [
      '-Wl,-L,@0@'.format(meson.project_source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.project_source_root(), rom_ext_linkfile_slot_a[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for slot A.
    [
      rom_ext_linkfile_slot_a,
    ],
  ],
  'rom_ext_slot_b' :
  [
    # Link arguments for slot B.
    [
      '-Wl,-L,@0@'.format(meson.project_source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.project_source_root(), rom_ext_linkfile_slot_b[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for slot B.
    [
      rom_ext_linkfile_slot_b,
    ],
  ],
  'rom_ext_virtual_addr' :
  [
    # Link arguments for pic.
    [
      '-Wl,-L,@0@'.format(meson.project_source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.project_source_root(), rom_ext_linkfile_virtual_addr[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for pic.
    [
      rom_ext_linkfile_virtual_addr,
    ],
  ],
}

rom_ext_slot_libs = {}
foreach slot, slot_link_args : rom_ext_link_info
  rom_ext_slot_libs += {
    slot: declare_dependency(
      sources: [
        'rom_ext_start.S',
        meson.project_source_root() / 'sw/device/silicon_creator/lib/base/static_critical_sec_mmio.c',
      ],
      link_args: slot_link_args[0],
      dependencies: [
        freestanding_headers,
        sw_silicon_creator_lib_base_sec_mmio,
        sw_silicon_creator_lib_driver_flash_ctrl,
        sw_silicon_creator_lib_driver_hmac,
        sw_silicon_creator_lib_driver_otp,
        sw_silicon_creator_lib_driver_pinmux,
        sw_silicon_creator_lib_driver_uart,
        sw_silicon_creator_lib_fake_deps,
        sw_silicon_creator_lib_log,
        sw_silicon_creator_lib_shutdown,
        sw_silicon_creator_lib_manifest_def,
        sw_silicon_creator_mask_rom_sigverify,
        sw_silicon_creator_rom_ext_epmp,
        sw_silicon_creator_rom_ext_boot_policy,
        sw_lib_crt,

      ],
      link_with: static_library(
        slot + '_rom_ext_lib',
        sources: [
          'rom_ext.c',
        ],
        link_depends: [slot_link_args[1]],
    )
  )
}
endforeach

foreach device_name, device_lib : sw_lib_arch_core_devices
  foreach slot, slot_lib : rom_ext_slot_libs
    rom_ext_elf = executable(
      slot + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        device_lib,
        slot_lib,
      ],
    )

    target_name = slot + '_@0@_' + device_name

    rom_ext_dis = custom_target(
      target_name.format('dis'),
      input: rom_ext_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    rom_ext_bin = custom_target(
      target_name.format('bin'),
      input: rom_ext_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    targets_to_export = [
      rom_ext_elf,
      rom_ext_dis,
      rom_ext_bin,
    ]

    foreach key_name, key_info : signing_keys
      signed_target_name = '_'.join(['rom_ext', slot, key_name, 'signed', '@0@', device_name])

      rom_ext_signed_bin = custom_target(
        signed_target_name.format('bin'),
        input: rom_ext_bin,
        output: '@BASENAME@.@0@.signed.bin'.format(key_name),
        command: [
          rom_ext_signer_export.full_path(),
          'rom_ext',
          '@INPUT@',
          key_info['path'],
          rom_ext_elf.full_path(),
          '@OUTPUT@',
        ],
        depends: rom_ext_signer_export,
        build_by_default: true,
      )

      rom_ext_signed_vmem32 = custom_target(
        signed_target_name.format('vmem32'),
        input: rom_ext_signed_bin,
        kwargs: bin_to_vmem32_custom_target_args,
      )

      rom_ext_signed_vmem64 = custom_target(
        signed_target_name.format('vmem64'),
        input: rom_ext_signed_bin,
        kwargs: bin_to_vmem64_custom_target_args,
      )

      rom_ext_signed_scr_vmem64 = custom_target(
        signed_target_name.format('scrambled'),
        input: rom_ext_signed_vmem64,
        output: flash_image_outputs,
        command: flash_image_command,
        depend_files: flash_image_depend_files,
        build_by_default: true,
      )

      targets_to_export += [
        rom_ext_signed_bin,
        rom_ext_signed_vmem32,
        rom_ext_signed_vmem64,
        rom_ext_signed_scr_vmem64,
      ]
    endforeach

    custom_target(
      target_name.format('export'),
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: targets_to_export,
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
