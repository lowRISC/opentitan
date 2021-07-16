# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

entropy_src_fw_ovr_test_lib = declare_dependency(
  link_with: static_library(
    'entropy_src_fw_ovr_test_lib',
    sources: ['entropy_src_fw_ovr_test.c'],
    dependencies: [
      sw_lib_dif_entropy,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'entropy_src_fw_ovr_test': {
    'library': entropy_src_fw_ovr_test_lib,
  }
}
