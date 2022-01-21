# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_crypto_ecdsa_p256_functest_lib = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_ecdsa_p256_functest_lib',
    sources: [
      'ecdsa_p256_functest.c'
    ],
    dependencies: [
      sw_lib_crypto_ecdsa_p256,
      sw_lib_driver_hmac,
      sw_lib_testing_entropy_testutils,
    ],
  ),
)
sw_tests += {
  'sw_lib_crypto_ecdsa_p256_functest': {
    'library': sw_lib_crypto_ecdsa_p256_functest_lib,
  }
}

# Tests for RSA-3072 verify
sw_lib_crypto_rsa_3072_verify_functest_lib = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_rsa_3072_verify_functest_lib',
    sources: [
      'rsa_3072_verify_functest.c',
      'rsa_3072_verify_testvectors.h'
    ],
    dependencies: [
      sw_lib_crypto_rsa_3072_verify,
      sw_lib_driver_hmac,
      sw_lib_testing_entropy_testutils,
    ],
  ),
)
sw_tests += {
  'sw_lib_crypto_rsa_3072_verify_functest': {
    'library': sw_lib_crypto_rsa_3072_verify_functest_lib,
  }
}
