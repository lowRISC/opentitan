# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# C wrapper for RSA-3072 verify
sw_lib_crypto_rsa_3072_verify = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_rsa_3072_verify',
    sources: [
      'rsa_3072_verify.c',
    ],
    dependencies: [
      sw_lib_crypto_otbn_util,
      sw_otbn['run_rsa_verify_3072']['rv32embed_dependency'],
    ],
  ),
)
