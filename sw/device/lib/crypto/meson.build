# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('drivers')

# OTBN interface
sw_lib_crypto_otbn_util = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_otbn_util',
    sources: [
      'otbn_util.c',
    ],
    dependencies: [
      sw_lib_crypto_otbn,
    ]
  )
)
