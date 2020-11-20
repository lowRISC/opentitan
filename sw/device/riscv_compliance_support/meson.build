# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  # We want to produce a single .a containing the libraries needed to run
  # the riscv-compliance test suite. Giving these libraries as dependcies
  # directly to static_library gives an empty library. Creating an 'inner'
  # library as below and then using link_whole to link against the 'inner'
  # library produces what we need.
  riscv_compliance_support_inner = static_library(
    'ot_riscv_compliance_support_inner_' + device_name,
    sources: ['support.c'],
    dependencies: [
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_irq_handlers,
      sw_lib_mem,
      sw_lib_testing_test_status,
      device_lib,
    ],
  )

  riscv_compliance_support = static_library(
    'ot_riscv_compliance_support_' + device_name,
    link_whole: [riscv_compliance_support_inner],
  )

  custom_target(
    'riscv_compliance_support_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [riscv_compliance_support],
    output: 'riscv_compliance_support_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
