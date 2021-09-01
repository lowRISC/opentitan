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
      '-Wl,-L,@0@'.format(meson.source_root()),
      '-Wl,-T,@0@/@1@'.format(meson.source_root(), rom_ext_linkfile_slot_b[0]),
    ] + embedded_target_extra_link_args,
    # Link dependency file for slot B.
    [
      rom_ext_linkfile_slot_b,
    ],
  ],
}

rom_ext_slot_libs = {}
foreach slot, slot_link_args : rom_ext_link_info
  rom_ext_slot_libs += {
    slot: declare_dependency(
      sources: [
        'rom_ext_start.S',
      ],
      link_args: slot_link_args[0],
      dependencies: [
        freestanding_headers,
        sw_lib_crt,
        sw_lib_dif_uart,
        sw_lib_runtime_hart,
        sw_lib_runtime_print,
        sw_silicon_creator_lib_base_sec_mmio,
        sw_silicon_creator_lib_manifest_section,

        # TODO: ePMP test status dependency should be removed from
        # production ROM_EXT. Tests should unlock the test status
        # address themselves (via a library or similar).
        sw_silicon_creator_lib_epmp_test_unlock,
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
      # TODO: at the moment we are not looking past "Silicon Creator" code,
      # however eventually there will be a transition to BL0 and/or kernel.
      # At this point we are assuming that the entry point will be `main`.
      sources: [
        'dummy_main.c',
      ]
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
  
    rom_ext_vmem32 = custom_target(
      target_name.format('vmem32'),
      input: rom_ext_bin,
      kwargs: bin_to_vmem32_custom_target_args,
    )
  
    rom_ext_vmem64 = custom_target(
      target_name.format('vmem64'),
      input: rom_ext_bin,
      kwargs: bin_to_vmem64_custom_target_args,
    )

    custom_target(
      target_name.format('export'),
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: [
        rom_ext_elf, 
        rom_ext_dis,
        rom_ext_bin,
        rom_ext_vmem32,
        rom_ext_vmem64,
      ],
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
