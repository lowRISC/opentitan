# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_otbn_sources += {
  'modexp': files(
    'modexp.s'
  ),
  'p256': files(
    'p256.s'
  ),
  'p256_base_mult_test': files(
    'p256_base_mult_test.s',
    'p256.s',
  ),
  'p256_ecdsa': files(
    'p256_ecdsa.s',
    'p256.s',
  ),
  'p256_ecdsa_sign_test': files(
    'p256_ecdsa_sign_test.s',
    'p256.s',
  ),
  'p256_ecdsa_verify_test': files(
    'p256_ecdsa_verify_test.s',
    'p256.s',
  ),
  'p256_isoncurve_test': files(
    'p256_isoncurve_test.s',
    'p256.s',
  ),
  'p256_proj_add_test': files(
    'p256_proj_add_test.s',
    'p256.s',
  ),
  'p256_scalar_mult_test': files(
    'p256_scalar_mult_test.s',
    'p256.s',
  ),
  'p384_base': files(
    'p384_base.s',
  ),
  'p384_base_mult_test': files(
    'p384_base_mult_test.s',
    'p384_sign.s',
    'p384_base.s',
  ),
  'p384_ecdsa_sign_test': files(
    'p384_ecdsa_sign_test.s',
    'p384_sign.s',
    'p384_base.s',
  ),
  'p384_ecdsa_verify_test': files(
    'p384_ecdsa_verify_test.s',
    'p384_verify.s',
    'p384_base.s',
  ),
  'p384_isoncurve_test': files(
    'p384_isoncurve_test.s',
    'p384_verify.s',
    'p384_base.s',
  ),
  'p384_proj_add_test': files(
    'p384_proj_add_test.s',
    'p384_base.s',
  ),
  'p384_scalar_mult_test': files(
    'p384_scalar_mult_test.s',
    'p384_sign.s',
    'p384_base.s',
  ),
  'p384_sign': files(
    'p384_sign.s',
    'p384_base.s',
  ),
  'p384_verify': files(
    'p384_verify.s',
    'p384_base.s',
  ),
  'rsa': files(
    'rsa.s',
    'modexp.s',
  ),
  'rsa_1024_dec_test': files(
    'rsa_1024_dec_test.s',
    'modexp.s',
  ),
  'rsa_1024_enc_test': files(
    'rsa_1024_enc_test.s',
    'modexp.s',
  ),
  'otbn_modexp': files(
    '../../vendor/veri-titan/gen/otbn_modexp.s',
  ),
  'rsa_verify_3072_consts_test': files(
    'rsa_verify_3072_consts_test.s',
    'rsa_verify_3072_rr.s',
    'rsa_verify_3072_m0inv.s',
    '../../vendor/veri-titan/gen/otbn_modexp.s',
  ),
  'rsa_verify_3072_m0inv': files(
    'rsa_verify_3072_m0inv.s',
  ),
  'rsa_verify_3072_rr': files(
    'rsa_verify_3072_rr.s',
    '../../vendor/veri-titan/gen/otbn_modexp.s',
  ),
  'rsa_verify_3072_test': files(
    'rsa_verify_3072_test.s',
    '../../vendor/veri-titan/gen/otbn_modexp.s',
  ),
  'rsa_verify': files(
    'rsa_verify.s',
  ),
  'rsa_verify_test': files(
    'rsa_verify_test.s',
    'rsa_verify.s',
  ),
  'rsa_verify_test_exp3': files(
    'rsa_verify_test_exp3.s',
    'rsa_verify.s',
  ),
  'run_rsa_verify_3072': files(
    'run_rsa_verify_3072.s',
    '../../vendor/veri-titan/gen/otbn_modexp.s',
    'rsa_verify_3072_m0inv.s',
    'rsa_verify_3072_rr.s',
  ),
  'run_rsa_verify_3072_rr_modexp': files(
    'run_rsa_verify_3072_rr_modexp.s',
    'rsa_verify_3072_rr.s',
    '../../vendor/veri-titan/gen/otbn_modexp.s',
  ),
}
