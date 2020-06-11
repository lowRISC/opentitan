# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All tests added to this dictionary will result in build targets that have
# names starting `sw/device/tests/<test_name>`. They will not contain the
# subdirectory name, because the build targets are really declared at the bottom
# of this file, rather than in the subdirectories.
sw_tests = {
  # 'test_name': test_lib,
}

subdir('dif')
subdir('sim_dv')

aes_test_lib = declare_dependency(
  link_with: static_library(
    'aes_test_lib',
    sources: ['aes_test.c'],
    dependencies: [
      sw_lib_aes,
      sw_lib_base_log,
    ],
  ),
)

flash_ctrl_test_lib = declare_dependency(
  link_with: static_library(
    'flash_ctrl_test_lib',
    sources: ['flash_ctrl_test.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_mmio,
      sw_lib_flash_ctrl,
      sw_lib_base_log,
    ],
  ),
)

rv_timer_test_lib = declare_dependency(
  link_with: static_library(
    'rv_timer_test_lib',
    sources: ['rv_timer_test.c'],
    dependencies: [
      sw_lib_irq,
      sw_lib_pinmux,
      sw_lib_rv_timer,
      sw_lib_base_log,
      sw_lib_dif_gpio,
    ],
  ),
)

sha256_test_lib = declare_dependency(
  link_with: static_library(
    'sha256_test_lib',
    sources: ['sha256_test.c'],
    dependencies: [
      sw_lib_hmac,
      sw_lib_flash_ctrl,
      sw_lib_base_log,
    ],
  ),
)

sw_tests += {
  'aes_test': aes_test_lib,
  'flash_ctrl_test': flash_ctrl_test_lib,
  'rv_timer_test': rv_timer_test_lib,
  'sha256_test': sha256_test_lib,
}

foreach sw_test_name, sw_test_lib : sw_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    sw_test_elf = executable(
      sw_test_name + '_' + device_name,
      sources: ['main.c'],
      name_suffix: 'elf',
      dependencies: [
        riscv_crt,
        device_lib,
        sw_test_lib,
        sw_lib_uart,
        sw_lib_irq_handlers,
        sw_lib_base_log,
        sw_lib_base_print,
        sw_lib_testing_test_status,
      ],
    )

    sw_test_embedded = custom_target(
      sw_test_name + '_' + device_name,
      command: make_embedded_target,
      input: sw_test_elf,
      output: make_embedded_target_outputs,
      build_by_default: true,
    )

    custom_target(
      sw_test_name + '_export_' + device_name,
      command: export_embedded_target,
      input: [sw_test_elf, sw_test_embedded],
      output: sw_test_name + '_export_' + device_name,
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
