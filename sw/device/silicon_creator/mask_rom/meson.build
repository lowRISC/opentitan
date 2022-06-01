# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Mask ROM Linker Parameters
#
# See `sw/device/lib/testing/test_framework/ottf.ld` for additional info
# about these parameters.

rom_linkfile = files(['mask_rom.ld'])
rom_link_args = [
  '-Wl,-L,@0@'.format(meson.project_source_root()),
  '-Wl,-T,@0@/@1@'.format(meson.project_source_root(), rom_linkfile[0]),
] + embedded_target_extra_link_args
rom_link_deps = [rom_linkfile]

# Signature verification.
sw_silicon_creator_mask_rom_sigverify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_mask_rom_sigverify',
    sources: [
      'sigverify_keys.c',
      hw_ip_otp_ctrl_reg_h,
    ],
    dependencies: [
      sw_silicon_creator_lib_sigverify,
      sw_silicon_creator_lib_driver_otp,
      sw_silicon_creator_lib_driver_rnd,
      sw_lib_bitfield,
    ],
  ),
)

# Mask ROM boot policy.
sw_silicon_creator_mask_rom_boot_policy = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_mask_rom_boot_policy',
    sources: [
      'boot_policy.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_manifest,
      sw_silicon_creator_lib_boot_data,
      sw_silicon_creator_lib_shutdown,
      sw_lib_hardened,
    ],
  ),
)

# Mask ROM ePMP library
sw_silicon_creator_mask_rom_epmp = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_mask_rom_epmp',
    sources: [
      'mask_rom_epmp_init.S',
      'mask_rom_epmp.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_epmp,
    ],
  )
)

# Mask ROM ePMP test library.
mask_rom_epmp_test_lib = declare_dependency(
  sources: [
    hw_ip_aon_timer_reg_h,
    hw_ip_ast_reg_h,
    hw_ip_clkmgr_reg_h,
    hw_ip_csrng_reg_h,
    hw_ip_edn_reg_h,
    hw_ip_entropy_src_reg_h,
    hw_ip_otp_ctrl_reg_h,
    hw_ip_pwrmgr_reg_h,
    hw_ip_sensor_ctrl_reg_h,
    hw_ip_sram_ctrl_reg_h,
    'mask_rom_start.S',
  ],
  link_args: rom_link_args,
  dependencies: [
    freestanding_headers,
    sw_silicon_creator_lib_base_sec_mmio,
    sw_silicon_creator_lib_driver_flash_ctrl,
    sw_silicon_creator_lib_driver_uart,
    sw_silicon_creator_lib_epmp_test_unlock,
    sw_silicon_creator_lib_irq_asm,
    sw_silicon_creator_mask_rom_epmp,
    sw_lib_crt,
    sw_lib_dif_sram_ctrl,
    sw_lib_runtime_print,
    sw_lib_testing_pinmux_testutils,
    sw_lib_testing_test_status,
  ],
  link_with: static_library(
    'mask_rom_epmp_test_lib',
    sources: [
      hw_ip_sram_ctrl_reg_h,
      hw_ip_flash_ctrl_reg_h,
      'mask_rom_epmp_test.c',
    ],
    link_depends: [rom_linkfile],
  )
)

# Mask ROM ePMP test images
foreach device_name, device_lib : sw_lib_arch_core_devices
  mask_rom_epmp_test_elf = executable(
    'mask_rom_epmp_test_' + device_name,
    name_suffix: 'elf',
    link_depends: rom_link_deps,
    link_args: [
      '-Wl,-Map=@0@/mask_rom_@1@.map'.format(meson.current_build_dir(), device_name),
    ],
    dependencies: [
      device_lib,
      mask_rom_epmp_test_lib,
    ],
  )

  target_name = 'mask_rom_epmp_test_@0@_' + device_name

  mask_rom_epmp_test_dis = custom_target(
    target_name.format('dis'),
    input: mask_rom_epmp_test_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  mask_rom_epmp_test_bin = custom_target(
    target_name.format('bin'),
    input: mask_rom_epmp_test_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  mask_rom_epmp_test_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: mask_rom_epmp_test_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  mask_rom_epmp_test_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: mask_rom_epmp_test_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  mask_rom_epmp_test_scrambled = custom_target(
    target_name.format('scrambled'),
    command: scramble_image_command,
    env: {'PYTHONPATH': meson.project_source_root()},
    depend_files: scramble_image_depend_files,
    input: mask_rom_epmp_test_elf,
    output: scramble_image_outputs,
    build_by_default: true,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      mask_rom_epmp_test_elf,
      mask_rom_epmp_test_dis,
      mask_rom_epmp_test_bin,
      mask_rom_epmp_test_vmem32,
      mask_rom_epmp_test_vmem64,
      mask_rom_epmp_test_scrambled,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach

sw_silicon_creator_mask_rom_bootstrap = declare_dependency(
  link_with: static_library (
    'sw_silicon_creator_mask_rom_bootstrap',
    sources: [
      'bootstrap.c',
      hw_ip_gpio_reg_h,
      hw_ip_flash_ctrl_reg_h,
      hw_ip_otp_ctrl_reg_h,
    ],
    dependencies: [
      sw_silicon_creator_lib_driver_flash_ctrl,
      sw_silicon_creator_lib_driver_otp,
      sw_silicon_creator_lib_driver_rstmgr,
      sw_silicon_creator_lib_driver_spi_device,
    ],
  ),
)

test('sw_silicon_creator_mask_rom_bootstrap_unittest', executable(
    'sw_silicon_creator_mask_rom_bootstrap_unittest',
    sources: [
      'bootstrap_unittest.cc',
      'bootstrap.c',
      hw_ip_gpio_reg_h,
      hw_ip_flash_ctrl_reg_h,
      hw_ip_otp_ctrl_reg_h,
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
      sw_lib_testing_hardened,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)

# MaskROM library.
mask_rom_lib = declare_dependency(
  sources: [
    hw_ip_aon_timer_reg_h,
    hw_ip_ast_reg_h,
    hw_ip_clkmgr_reg_h,
    hw_ip_csrng_reg_h,
    hw_ip_edn_reg_h,
    hw_ip_entropy_src_reg_h,
    hw_ip_otp_ctrl_reg_h,
    hw_ip_pwrmgr_reg_h,
    hw_ip_sensor_ctrl_reg_h,
    hw_ip_sram_ctrl_reg_h,
    'mask_rom_start.S',
    meson.project_source_root() / 'sw/device/silicon_creator/lib/base/static_critical_sec_mmio.c',
  ],
    link_args: rom_link_args,
    dependencies: [
      freestanding_headers,
      sw_silicon_creator_lib_driver_hmac,
      sw_silicon_creator_lib_driver_flash_ctrl,
      sw_silicon_creator_lib_driver_ibex,
      sw_silicon_creator_lib_driver_keymgr,
      sw_silicon_creator_lib_driver_lifecycle,
      sw_silicon_creator_lib_driver_otp,
      sw_silicon_creator_lib_driver_pinmux,
      sw_silicon_creator_lib_driver_retention_sram,
      sw_silicon_creator_lib_driver_rnd,
      sw_silicon_creator_lib_driver_rstmgr,
      sw_silicon_creator_lib_driver_uart,
      sw_silicon_creator_lib_driver_watchdog,
      sw_silicon_creator_lib_irq_asm,
      sw_silicon_creator_lib_log,
      sw_silicon_creator_lib_manifest,
      sw_silicon_creator_lib_shutdown,
      sw_silicon_creator_mask_rom_boot_policy,
      sw_silicon_creator_mask_rom_bootstrap,
      sw_silicon_creator_mask_rom_epmp,
      sw_silicon_creator_mask_rom_sigverify,
      sw_lib_crt,
    ],
    link_with: static_library(
      'mask_rom_lib',
      sources: [
        hw_ip_otp_ctrl_reg_h,
        'mask_rom.c',
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
    env: {'PYTHONPATH': meson.project_source_root()},
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

test('sw_silicon_creator_mask_rom_boot_policy_unittest', executable(
    'sw_silicon_creator_mask_rom_boot_policy_unittest',
    sources: [
      'boot_policy_unittest.cc',
      'boot_policy.c',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_hardened,
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
      '../lib/sigverify/mod_exp_otbn_mock.cc',
      hw_ip_otp_ctrl_reg_h,
    ] + sw_silicon_creator_lib_sigverify_sources_for_boot_stage_tests,
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
      sw_lib_testing_hardened,
      sw_lib_testing_memory,
    ],
    native: true,
    c_args: ['-DOT_OFF_TARGET_TEST'],
    cpp_args: ['-DOT_OFF_TARGET_TEST'],
  ),
  suite: 'mask_rom',
)
