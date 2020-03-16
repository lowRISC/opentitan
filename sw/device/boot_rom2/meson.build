# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# We re-use a bunch of variables from boot_rom/meson.build for now.
# These are:
# - chip_info_h
# - rom_link_args
# - rom_link_deps

sw_br2_crt_files = [
  '../boot_rom/rom_crt.S',
  '../boot_rom/irq_vector.S',
]

sw_br2_log = declare_dependency(
  link_with: static_library(
    'sw_br2_log',
    sources: ['uart_log.c'],
    dependencies: [
      dif_uart,
      sw_lib_mem,
      sw_lib_base_print,
      sw_lib_runtime_hart,
    ],
  ),
)

foreach device_name, device_lib : sw_lib_arch_core_devices
  sw_br2_elf = executable(
    'br2_' + device_name,
    sources: [
      'boot_rom.c',
      sw_br2_crt_files,
    ],
    name_suffix: 'elf',
    link_args: rom_link_args,
    link_depends: rom_link_deps,
    dependencies: [
      chip_info_h,
      device_lib,
      sw_br2_log,
      sw_lib_base_log,

      # Non-DIF drivers. These should eventally be removed.
      sw_lib_pinmux,
    ],
  )

  sw_br2_embedded = custom_target(
    'br2_' + device_name,
    command: make_embedded_target,
    input: sw_br2_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'br2_export_' + device_name,
    command: export_embedded_target,
    input: [sw_br2_elf, sw_br2_embedded],
    output: 'br2_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
