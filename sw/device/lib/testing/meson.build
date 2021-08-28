# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# hardware entropy complex (entropy_src, csrng, edn) test utilities.
sw_lib_testing_entropy_testutils_lib = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_entropy_testutils_lib',
    sources: [
      hw_ip_edn_reg_h,
      'entropy_testutils.c'
    ],
    dependencies: [
      top_earlgrey,
      sw_lib_mmio,
      sw_lib_dif_entropy_src,
      sw_lib_dif_csrng,
      top_earlgrey,
    ],
  ),
)

# Random number generator.
sw_lib_testing_random = declare_dependency(
  link_with: static_library(
    'random_ot',
    sources: ['random.c'],
  )
)

subdir('test_framework')
