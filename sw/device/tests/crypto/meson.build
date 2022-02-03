# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

crypto_ecdsa_p256_test_lib = declare_dependency(
  link_with: static_library(
    'crypto_ecdsa_p256_test_lib',
    sources: [
      'ecdsa_p256_functest.c'
    ],
    dependencies: [
      sw_lib_crypto_ecdsa_p256,
      sw_lib_crypto_hmac,
      sw_lib_testing_entropy_testutils,
    ],
  ),
)
sw_tests += {
  'crypto_ecdsa_p256_test': {
    'library': crypto_ecdsa_p256_test_lib,
  }
}

crypto_ecdsa_p256_verify_test_lib = declare_dependency(
  link_with: static_library(
    'crypto_ecdsa_p256_verify_test_lib',
    sources: [
      'ecdsa_p256_verify_functest.c'
    ],
    dependencies: [
      sw_lib_crypto_ecdsa_p256,
      sw_lib_crypto_hmac,
    ],
  ),
)
sw_tests += {
  'crypto_ecdsa_p256_verify_test': {
    'library': crypto_ecdsa_p256_verify_test_lib,
  }
}

# Tests for RSA-3072 verify
crypto_rsa_3072_verify_test_lib = declare_dependency(
  link_with: static_library(
    'crypto_rsa_3072_verify_test_lib',
    sources: [
      'rsa_3072_verify_functest.c',
      'rsa_3072_verify_testvectors.h'
    ],
    dependencies: [
      sw_lib_crypto_rsa_3072_verify,
      sw_lib_crypto_hmac,
    ],
  ),
)
sw_tests += {
  'crypto_rsa_3072_verify_test': {
    'library': crypto_rsa_3072_verify_test_lib,
  }
}
