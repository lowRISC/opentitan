# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All tests added to this dictionary will result in build targets that have
# names starting `sw/device/tests/mask_rom/<test_name>`. They will not contain
# the subdirectory name, because the build targets are really declared at the
# bottom of this file, rather than in the subdirectories.
mask_rom_tests = {
  # 'mask_rom_test_name': mask_rom_test_lib,
}

mask_rom_dummy_test_lib = declare_dependency(
  link_with: static_library(
    'mask_rom_dummy_test_lib',
    sources: ['mask_rom_dummy_test.c'],
  ),
)
mask_rom_tests += { 'mask_rom_dummy': mask_rom_dummy_test_lib }

foreach mask_rom_test_name, mask_rom_test_lib : mask_rom_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    mask_rom_test_elf = executable(
      mask_rom_test_name + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        mask_rom_crt,
        device_lib,
        mask_rom_test_lib,
        sw_lib_testing_test_main,
        sw_lib_mem,
      ],
    )

    mask_rom_test_embedded = custom_target(
      mask_rom_test_name + '_' + device_name,
      command: make_embedded_target,
      input: mask_rom_test_elf,
      output: make_embedded_target_outputs,
      build_by_default: true,
    )

    custom_target(
      mask_rom_test_name + '_export_' + device_name,
      command: export_embedded_target,
      input: [mask_rom_test_elf, mask_rom_test_embedded],
      output: mask_rom_test_name + '_export_' + device_name,
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach