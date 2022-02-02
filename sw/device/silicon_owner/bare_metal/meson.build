# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Linker Parameters
#
# See `sw/device/lib/testing/test_framework/ottf.ld` for additional info
# about these parameters.

bare_metal_linkfile_slot_a = files(['bare_metal_slot_a.ld'])
bare_metal_linkfile_slot_b = files(['bare_metal_slot_b.ld'])

bare_metal_link_info = {
  'bare_metal_slot_a' :
  [
    # Link arguments for slot A.
    [
      '-Wl,-L,@0@'.format(meson.source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.source_root(), bare_metal_linkfile_slot_a[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for slot A.
    [
      bare_metal_linkfile_slot_a,
    ],
  ],
  'bare_metal_slot_b' :
  [
    # Link arguments for slot B.
    [
      '-Wl,-L,@0@'.format(meson.source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.source_root(), bare_metal_linkfile_slot_b[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for slot B.
    [
      bare_metal_linkfile_slot_b,
    ],
  ],
}

bare_metal_slot_libs = {}
foreach slot, slot_link_args : bare_metal_link_info
  bare_metal_slot_libs += {
    slot: declare_dependency(
      sources: [
        'bare_metal_start.S',
      ],
      link_args: slot_link_args[0],
      dependencies: [
        freestanding_headers,
        sw_silicon_creator_lib_driver_pinmux,
        sw_silicon_creator_lib_driver_uart,
        sw_silicon_creator_lib_fake_deps,
        sw_silicon_creator_lib_manifest_section,
        sw_lib_crt,
        sw_lib_runtime_print,

      ],
      link_with: static_library(
        slot + '_bare_metal_lib',
        sources: [
          'bare_metal_example.c',
        ],
        link_depends: [slot_link_args[1]],
    )
  )
}
endforeach

foreach device_name, device_lib : sw_lib_arch_core_devices
  foreach slot, slot_lib : bare_metal_slot_libs
    bare_metal_elf = executable(
      slot + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        device_lib,
        slot_lib,
      ],
    )

    target_name = slot + '_@0@_' + device_name

    bare_metal_dis = custom_target(
      target_name.format('dis'),
      input: bare_metal_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    bare_metal_bin = custom_target(
      target_name.format('bin'),
      input: bare_metal_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    targets_to_export = [
      bare_metal_elf,
      bare_metal_dis,
      bare_metal_bin,
    ]

    foreach key_name, key_info : signing_keys
      signed_target_name = '_'.join(['bare_metal', slot, key_name, 'signed', '@0@', device_name])

      bare_metal_signed_bin = custom_target(
        signed_target_name.format('bin'),
        input: bare_metal_bin,
        output: '@BASENAME@.@0@.signed.bin'.format(key_name),
        command: [
          rom_ext_signer_export.full_path(),
          'owner',
          '@INPUT@',
          key_info['path'],
          bare_metal_elf.full_path(),
          '@OUTPUT@',
        ],
        depends: rom_ext_signer_export,
        build_by_default: true,
      )

      bare_metal_signed_vmem32 = custom_target(
        signed_target_name.format('vmem32'),
        input: bare_metal_signed_bin,
        kwargs: bin_to_vmem32_custom_target_args,
      )

      bare_metal_signed_vmem64 = custom_target(
        signed_target_name.format('vmem64'),
        input: bare_metal_signed_bin,
        kwargs: bin_to_vmem64_custom_target_args,
      )

      targets_to_export += [
        bare_metal_signed_bin,
        bare_metal_signed_vmem32,
        bare_metal_signed_vmem64,
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
