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

# RISC-V startup library. Every RISC-V executable should depend on this target.
rom_ext_crt = declare_dependency(
  link_args: rom_ext_link_args,
  # The following assembly files need to be included as a source, not a
  # static library, so that their custom sections can be picked up when
  # linking.
  sources: [
    # This contains the contents of the `.crt` section which does the initial
    # setup before jumping to `rom_ext_start_boot`.
    'rom_ext_start.S',
  ],
  # This argument exists solely so that Meson realizes that riscv_linker_script
  # is part of the dependency graph. This seems to be the only way to convince
  # Meson to behave in this way, for the following reasons:
  # - The dependencies arg can only include artifacts from declare_dependency().
  # - We can't put linker scripts into the sources list, since Meson has no
  #   clue how to deal with them.
  # - custom_target() doesn't help, because we can't convince Meson to depend on
  #   a custom_target() unless it produces source files.
  # - If we go with static_library, sources needs to be non-empty in order for
  #   Meson to correctly treat it as a cross-compile target (otherwise, we get
  #   linker errors). This is because Meson guesses the type of a target based
  #   off of the file extensions of the source files.
  link_with: static_library(
    'rom_exts_linker_script_dep_shim',
    sources: ['empty.c'],
    link_depends: [rom_ext_linkfile],
  )
)

foreach device_name, device_lib : sw_lib_arch_core_devices
  rom_ext_elf = executable(
    'rom_ext_' + device_name,
    sources: [
      'rom_ext_manifest.S',
    ],
    name_suffix: 'elf',
    dependencies: [
      device_lib,
      rom_ext_crt,
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
