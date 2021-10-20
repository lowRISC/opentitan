# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_silicon_creator_lib_crypto_ecdsa_p256_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_crypto_ecdsa_p256_functest',
    sources: [
      'ecdsa_p256_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_crypto_ecdsa_p256,
      sw_silicon_creator_lib_driver_hmac,
      sw_lib_testing_entropy_testutils,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_crypto_ecdsa_p256_functest': {
    'library': sw_silicon_creator_lib_crypto_ecdsa_p256_functest,
  }
}

sw_silicon_creator_lib_crypto_rsa_3072_verify_functest = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_crypto_rsa_3072_verify_functest',
    sources: [
      'rsa_3072_verify_functest.c'
    ],
    dependencies: [
      sw_silicon_creator_lib_crypto_rsa_3072_verify,
      sw_silicon_creator_lib_driver_hmac,
      sw_lib_testing_entropy_testutils,
    ],
  ),
)
mask_rom_tests += {
  'sw_silicon_creator_lib_crypto_rsa_3072_verify_functest': {
    'library': sw_silicon_creator_lib_crypto_rsa_3072_verify_functest,
  }
}
