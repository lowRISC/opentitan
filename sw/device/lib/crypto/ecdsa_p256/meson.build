# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# C wrapper for ECDSA sign/verify
sw_silicon_creator_lib_crypto_ecdsa_p256 = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_crypto_ecdsa_p256',
    sources: [
      'ecdsa_p256.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_otbn_util,
      sw_otbn['p256_ecdsa']['rv32embed_dependency'],
    ],
  ),
)
