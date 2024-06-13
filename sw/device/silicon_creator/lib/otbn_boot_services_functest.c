// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

// Keymgr handle for this test.
static dif_keymgr_t keymgr;

// Message value for signature generation/verification tests.
const char kTestMessage[] = "Test message.";
const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Valid ECDSA-P256 public key.
static const ecdsa_p256_public_key_t kEcdsaKey = {
    .x = {0x1ceb402b, 0x9dc600d1, 0x182ec21b, 0x5ede3640, 0x3566bdac,
          0x1debf94b, 0x1a286a75, 0x8904d749},
    .y = {0x63eab6dc, 0x0c53bf99, 0x086d3ee7, 0x1076efa6, 0x8dd8ece2,
          0xbfececf0, 0x9b94e34d, 0x59b12f3c},
};

// Valid ECDSA-P256 signature for `kTestMessage`.
static const ecdsa_p256_signature_t kEcdsaSignature = {
    .r = {0x4811545a, 0x088d927b, 0x5d8624b5, 0x2ef1f329, 0x184ba14a,
          0xf655eede, 0xaaed0d54, 0xa20e1ac7},
    .s = {0x729b945d, 0x181dc116, 0x1025dba4, 0xb99828a0, 0xe7225df3,
          0x0e200e9b, 0x785690b4, 0xf47efe98}};

// Sample key manager diversification data for testing.
static const sc_keymgr_diversification_t kDiversification = {
    .salt = {0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0xf0f1f2f3,
             0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff},
    .version = 0,
};

// Test values for attestation key seeds.
static const uint32_t kSeedValues[3][kAttestationSeedWords] = {
    {0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f, 0x80818283, 0x84858687,
     0x88898a8b, 0x8c8d8e8f, 0x90b1b2b3, 0x94959697},
    {0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7,
     0xb8b9babb, 0xbcbdbebf, 0xc0b1b2b3, 0xc4c5c6c7},
    {0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf, 0xe0e1e2e3, 0xe4e5e6e7,
     0xe8e9eaeb, 0xecedeeef, 0xf0b1b2b3, 0xf4f5f6f7},
};

rom_error_t sigverify_test(void) {
  // Hash the test message.
  hmac_digest_t digest;
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);

  // The recovered `r` value from sigverify should be equal to the signature
  // `r` value.
  uint32_t recovered_r[kEcdsaP256SignatureComponentWords];
  RETURN_IF_ERROR(
      otbn_boot_sigverify(&kEcdsaKey, &kEcdsaSignature, &digest, recovered_r));
  CHECK_ARRAYS_EQ(recovered_r, kEcdsaSignature.r, ARRAYSIZE(kEcdsaSignature.r));
  return kErrorOk;
}

rom_error_t attestation_keygen_test(void) {
  // Check that key generations with different seeds result in different keys.
  ecdsa_p256_public_key_t pk_uds;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                               kOtbnBootAttestationKeyTypeDice,
                                               kDiversification, &pk_uds));
  ecdsa_p256_public_key_t pk_cdi0;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kCdi0AttestationKeySeed,
                                               kOtbnBootAttestationKeyTypeDice,
                                               kDiversification, &pk_cdi0));
  ecdsa_p256_public_key_t pk_cdi1;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kCdi1AttestationKeySeed,
                                               kOtbnBootAttestationKeyTypeDice,
                                               kDiversification, &pk_cdi1));
  ecdsa_p256_public_key_t pk_tpm_ek;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kTpmEkAttestationKeySeed,
                                               kOtbnBootAttestationKeyTypeTpm,
                                               kDiversification, &pk_tpm_ek));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds, (unsigned char *)&pk_cdi0,
                  sizeof(pk_uds));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds, (unsigned char *)&pk_cdi1,
                  sizeof(pk_uds));
  CHECK_ARRAYS_NE((unsigned char *)&pk_cdi0, (unsigned char *)&pk_cdi1,
                  sizeof(pk_uds));
  CHECK_ARRAYS_NE((unsigned char *)&pk_tpm_ek, (unsigned char *)&pk_cdi1,
                  sizeof(pk_uds));

  // Check that running the same key generation twice results in the same key.
  ecdsa_p256_public_key_t pk_uds_again;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, kOtbnBootAttestationKeyTypeDice, kDiversification,
      &pk_uds_again));
  CHECK_ARRAYS_EQ((unsigned char *)&pk_uds_again, (unsigned char *)&pk_uds,
                  sizeof(pk_uds));

  // Check that key generations with different diversification result in
  // different keys.
  sc_keymgr_diversification_t diversification_modified;
  memcpy(&diversification_modified, &kDiversification,
         sizeof(diversification_modified));
  diversification_modified.salt[0] ^= 1;
  ecdsa_p256_public_key_t pk_uds_div;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      diversification_modified, &pk_uds_div));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds_div, (unsigned char *)&pk_uds,
                  sizeof(pk_uds));
  return kErrorOk;
}

rom_error_t attestation_advance_and_endorse_test(void) {
  // Generate and save the a keypair.
  ecdsa_p256_public_key_t pk;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                               kOtbnBootAttestationKeyTypeDice,
                                               kDiversification, &pk));
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kUdsAttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      kDiversification));

  // Advance keymgr to the next stage.
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey));
  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));

  // Run endorsement (should overwrite the key with randomness when done).
  hmac_digest_t digest;
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);
  ecdsa_p256_signature_t sig;
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // Check that the signature is valid (recovered r == r).
  uint32_t recovered_r[kEcdsaP256SignatureComponentWords];
  RETURN_IF_ERROR(otbn_boot_sigverify(&pk, &sig, &digest, recovered_r));
  CHECK_ARRAYS_EQ(recovered_r, sig.r, ARRAYSIZE(sig.r));

  // Run endorsement again (should not return an error, but should produce an
  // invalid signature).
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // Check that the signature is invalid (recovered r != r).
  RETURN_IF_ERROR(otbn_boot_sigverify(&pk, &sig, &digest, recovered_r));
  CHECK_ARRAYS_NE(recovered_r, sig.r, ARRAYSIZE(sig.r));

  return kErrorOk;
}

// N.B. This test will lock OTBN, so it needs to be the last test that runs.
rom_error_t attestation_save_clear_key_test(void) {
  // Save and then clear a private key.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kUdsAttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      kDiversification));
  RETURN_IF_ERROR(otbn_boot_attestation_key_clear());

  // Save the private key again and check that endorsing succeeds.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kUdsAttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      kDiversification));
  hmac_digest_t digest;
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);
  ecdsa_p256_signature_t sig;
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // Clear the key and check that endorsing now fails (it should even lock
  // OTBN).
  RETURN_IF_ERROR(otbn_boot_attestation_key_clear());
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);
  CHECK(otbn_boot_attestation_endorse(&digest, &sig) ==
        kErrorOtbnExecutionFailed);
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex, KMAC, and the key manager.
  CHECK_STATUS_OK(entropy_complex_init());
  dif_kmac_t kmac;
  CHECK_STATUS_OK(keymgr_testutils_startup(&keymgr, &kmac));
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey));

  // Initialize flash.
  dif_flash_ctrl_state_t flash_ctrl;
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash_ctrl));

  // Program the attestation key seeds in flash. The setup step only needs to
  // be done once, since the seeds are on the same page.
  flash_info_field_t seed_fields[] = {
      kFlashInfoFieldUdsAttestationKeySeed,
      kFlashInfoFieldCdi0AttestationKeySeed,
      kFlashInfoFieldCdi1AttestationKeySeed,
  };
  uint32_t page_address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_scrambled_setup(
      &flash_ctrl, seed_fields[0].page, seed_fields[0].bank,
      seed_fields[0].partition, &page_address));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_ctrl, page_address, seed_fields[0].partition, kSeedValues[0],
      kDifFlashCtrlPartitionTypeInfo, kAttestationSeedWords));
  CHECK(ARRAYSIZE(seed_fields) == ARRAYSIZE(kSeedValues));
  for (size_t i = 1; i < ARRAYSIZE(seed_fields); i++) {
    CHECK(seed_fields[i].page == seed_fields[i - 1].page);
    CHECK(seed_fields[i].bank == seed_fields[i - 1].bank);
    CHECK(seed_fields[i].partition == seed_fields[i - 1].partition);
    CHECK_STATUS_OK(flash_ctrl_testutils_write(
        &flash_ctrl, page_address + seed_fields[i].byte_offset,
        seed_fields[i].partition, kSeedValues[i],
        kDifFlashCtrlPartitionTypeInfo, kAttestationSeedWords));
  }

  // Load the boot services OTBN app.
  CHECK(otbn_boot_app_load() == kErrorOk);

  EXECUTE_TEST(result, sigverify_test);
  EXECUTE_TEST(result, attestation_keygen_test);
  EXECUTE_TEST(result, attestation_advance_and_endorse_test);
  EXECUTE_TEST(result, attestation_save_clear_key_test);

  return status_ok(result);
}
