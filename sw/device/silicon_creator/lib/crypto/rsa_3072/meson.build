# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# C wrapper for RSA-3072 modexp
sw_silicon_creator_lib_crypto_rsa_3072_verify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_crypto_rsa_3072_modexp',
    sources: [
      'rsa_3072_modexp.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_otbn_util,
      sw_otbn['run_rsa_verify_3072_rr_modexp']['rv32embed_dependency'],
    ],
  ),
)

# C wrapper for RSA-3072 verify
sw_silicon_creator_lib_crypto_rsa_3072_verify = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_crypto_rsa_3072_verify',
    sources: [
      'rsa_3072_verify.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_otbn_util,
      sw_otbn['run_rsa_verify_3072']['rv32embed_dependency'],
    ],
  ),
)
