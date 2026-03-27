// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"

static rom_error_t owner_verify_spx_signature_not_found_test(void) {
  owner_keydata_t key = {0};
  hmac_digest_t digest = {0};
  uint32_t flash_exec = 0;
  rom_error_t error =
      owner_verify(kOwnershipKeyAlgCategorySpx, &key, NULL, NULL, NULL, 0, NULL,
                   0, NULL, 0, &digest, &flash_exec);
  if (error != kErrorSigverifySpxNotFound) {
    LOG_ERROR("error must be 0x%08x, not 0x%08x", kErrorSigverifySpxNotFound,
              error);
    return kErrorUnknown;
  }
  return kErrorOk;
}

static rom_error_t owner_verify_bad_spx_config_test(void) {
  owner_keydata_t key = {0};
  hmac_digest_t digest = {0};
  uint32_t key_alg = kOwnershipKeyAlgCategorySpx | kOwnershipKeyAlgSpxPure |
                     kOwnershipKeyAlgSpxPrehash;
  sigverify_spx_signature_t spx_signature = {0};
  uint32_t flash_exec = 0;
  rom_error_t error = owner_verify(key_alg, &key, NULL, &spx_signature, NULL, 0,
                                   NULL, 0, NULL, 0, &digest, &flash_exec);
  if (error != kErrorSigverifyBadSpxConfig) {
    LOG_ERROR("error must be 0x%08x, not 0x%08x", kErrorSigverifyBadSpxConfig,
              error);
    return kErrorUnknown;
  }
  return kErrorOk;
}

static rom_error_t owner_verify_bad_spx_signature_test(void) {
  owner_keydata_t key = {0};
  hmac_digest_t digest = {0};
  uint32_t key_alg = kOwnershipKeyAlgSpxPure;
  sigverify_spx_signature_t spx_signature = {0};
  uint32_t flash_exec = 0;
  rom_error_t error = owner_verify(key_alg, &key, NULL, &spx_signature, NULL, 0,
                                   NULL, 0, NULL, 0, &digest, &flash_exec);
  if (error != kErrorSigverifyBadSpxSignature) {
    LOG_ERROR("error must be 0x%08x, not 0x%08x",
              kErrorSigverifyBadSpxSignature, error);
    return kErrorUnknown;
  }
  return kErrorOk;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t error = OK_STATUS();

  EXECUTE_TEST(error, owner_verify_spx_signature_not_found_test);
  EXECUTE_TEST(error, owner_verify_bad_spx_config_test);
  EXECUTE_TEST(error, owner_verify_bad_spx_signature_test);

  return status_ok(error);
}
