# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

otbn_rsa_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_rsa_test_lib',
    sources: ['otbn_rsa_test.c'],
    dependencies: [
      sw_lib_runtime_otbn,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      top_earlgrey,
      sw_otbn['rsa']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_rsa_test': {
    'library': otbn_rsa_test_lib
  }
}
