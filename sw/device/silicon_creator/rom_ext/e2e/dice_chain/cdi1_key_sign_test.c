// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

OTTF_DEFINE_TEST_CONFIG();

static rom_error_t sign_with_cdi1(void) {
  // Compute the CDI_0 public key.
  ecdsa_p256_public_key_t pk_cdi0;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier, &pk_cdi0));

  // Compute the CDI_1 public key and side-load the CDI_1 private key into OTBN
  // to preapre for otbn_boot_attestation_endorse.
  ecdsa_p256_public_key_t pk_cdi1;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier, &pk_cdi1));

  // Create a digest to sign. Specific contents don't matter so use the CDI_1
  // public key for convenience.
  hmac_digest_t digest;
  hmac_sha256(&pk_cdi1, sizeof(pk_cdi1), &digest);

  // Sign the digest with CDI_1.
  ecdsa_p256_signature_t sig;
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // Digest should verify correctly with CDI_1 public key.
  uint32_t recovered_r_cdi1[kEcdsaP256SignatureComponentWords];
  RETURN_IF_ERROR(
      otbn_boot_sigverify(&pk_cdi1, &sig, &digest, recovered_r_cdi1));
  CHECK_ARRAYS_EQ(recovered_r_cdi1, sig.r, ARRAYSIZE(sig.r));

  // Digest should fail to verify with CDI_0 public key.
  uint32_t recovered_r_cdi0[kEcdsaP256SignatureComponentWords];
  RETURN_IF_ERROR(
      otbn_boot_sigverify(&pk_cdi0, &sig, &digest, recovered_r_cdi0));
  CHECK_ARRAYS_NE(recovered_r_cdi0, sig.r, ARRAYSIZE(sig.r));

  // Clear the key for correctness.
  RETURN_IF_ERROR(otbn_boot_attestation_key_clear());

  return kErrorOk;
}

bool test_main(void) {
#ifdef EMPTY_TEST_MSG
  LOG_INFO(EMPTY_TEST_MSG);
#endif

  rom_error_t status = sign_with_cdi1();
  if (status != kErrorOk) {
    LOG_INFO("FAIL", status);
  }

  LOG_INFO("PASS");

  return true;
}
