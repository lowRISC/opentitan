# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# HMAC driver
sw_lib_crypto_hmac = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'hmac.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_lib_bitfield,
      top_earlgrey,
    ]
  )
)

# OTBN driver
sw_lib_crypto_otbn = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_otbn',
    sources: [
      hw_ip_otbn_reg_h,
      'otbn.c',
    ],
    dependencies: [
      sw_lib_abs_mmio,
      sw_lib_bitfield,
      top_earlgrey,
    ]
  )
)
