// Copyright lowRISC contributors.
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

// sw/device/silicon_creator/rom/keys/fake/test_key_0_rsa_3072_exp_f4.public.der
static const sigverify_rsa_key_t kRsaKey = {
    .n = {{
        0x5801a2bd, 0xeff64a46, 0xc8cf2251, 0xa7cd62cb, 0x634a39c2, 0x55c936d3,
        0x463d61fc, 0x762ebbaa, 0x01aadfb2, 0x23da15d1, 0x8475fdc6, 0x4ec67b7b,
        0xe9364570, 0xd23ec7c7, 0x98038d63, 0x5688a56b, 0x68037add, 0xb20ff289,
        0x9d96c1ce, 0xbac0b8cd, 0xead33d0b, 0x195f89c8, 0xd7dc110e, 0xf5bccc12,
        0x8dfa33dc, 0xedc404d2, 0x74ef8524, 0x9197c0c8, 0x79cc448e, 0x4c9c505d,
        0x4a586ad7, 0xe2d0f071, 0x589f28c2, 0x2ca7fc22, 0x0354b0e2, 0xefb63b44,
        0x33a75b04, 0x9e194454, 0x1b4b2cde, 0x8e3f78e0, 0x5260877c, 0x05685b72,
        0x4868ad4e, 0x10303ac9, 0x05ac2411, 0x5e797381, 0xd5407668, 0xe3522348,
        0xa33134f8, 0x38f7a953, 0xd926f672, 0x136f6753, 0xb186b0ab, 0x5ccab586,
        0x61e5bf2e, 0x9fc0eebb, 0x788ed0bd, 0x47b5fc70, 0xf971262a, 0x3b40d99b,
        0x5b9fd926, 0xce3c93bf, 0xd406005e, 0x72b9e555, 0xc9b9273e, 0xfcef747f,
        0xf0a35598, 0x2761e8f6, 0xec1799df, 0x462bc52d, 0x8e47218b, 0x429ccdae,
        0xe7e7d66c, 0x70c70b03, 0x0356c3d2, 0x3cb3e7d1, 0xd42d035d, 0x83c529a3,
        0x8df9930e, 0xb082e1f0, 0x07509c30, 0x5c33a350, 0x4f6884b9, 0x7b9d2de0,
        0x0f1d16b3, 0x38dbcf55, 0x168580ea, 0xc2f2aca4, 0x43f0ae60, 0x227dd2ed,
        0xd8dc61f4, 0x9404e8bc, 0x0db76fe3, 0x3491d3b0, 0x6ca44e27, 0xcda63719,
    }},
    .n0_inv =
        {
            0x9c9a176b,
            0x44d6fa52,
            0x71a63ec4,
            0xadc94595,
            0x3fd9bc73,
            0xa83cdc95,
            0xbe1bc819,
            0x2b421fae,
        },
};

// Signature for "test message".
static const sigverify_rsa_buffer_t kRsaSignature = {
    .data = {
        0x725bfa2c, 0xdb359e00, 0x4dd50e25, 0x344ce68a, 0x2d49dc6b, 0x4a53a013,
        0x2abd4a7c, 0x762dd4aa, 0xe1935a41, 0xb807b2c2, 0xdf0222d7, 0x2dc12fdf,
        0xe432fb54, 0x2a12e15d, 0xf290eb01, 0x2529d6d4, 0x0813ab70, 0x78bd8229,
        0x63f3064e, 0x1cceba14, 0x4beff42b, 0xb9e98de4, 0x84a7f442, 0xb03649bc,
        0x7726af3d, 0xeaf2656d, 0xf82f963b, 0x31082a3d, 0x194ff701, 0x86588b75,
        0x5732f5de, 0x35d14195, 0x262c612d, 0x3f66ce59, 0xa2742c75, 0x276341fb,
        0x8cb84d0a, 0x1222f7f6, 0xbbd8ec56, 0x36e629b1, 0x891fd231, 0xfb351d0c,
        0x598dab98, 0x64534c32, 0xbcc39e4c, 0x256e4544, 0x3a3205ab, 0x02c5878c,
        0x99a7e70a, 0xc65c4d5d, 0xe5bedc24, 0x83de5d15, 0x16429111, 0x05d0b216,
        0xbf8d4dfe, 0x4be3707f, 0x004d6b75, 0xd64b4c66, 0x6e9e4375, 0xa5e1fc9f,
        0x4ca3c8f2, 0x544cf3d2, 0x34767ef2, 0xc361639c, 0x6062f836, 0x558ebb62,
        0xec7ee0af, 0x11033e71, 0x873742d3, 0x0ad49285, 0x6f163385, 0xd880305f,
        0x76e79003, 0x2bd4c955, 0x4a00fd2a, 0x7a045dd4, 0xdf671f3f, 0xd986e081,
        0x96cfc193, 0xd211ece5, 0x4486f7cb, 0x47be12f5, 0xe513619c, 0xe1a5f41c,
        0xbc4fbcb3, 0x78b903b7, 0xc8dcbff8, 0x5c088a19, 0x66301acc, 0x12b05bf9,
        0xa9c795a9, 0xe229e3ca, 0xe928d10b, 0x96eda9d9, 0x162f4a58, 0x069b950c,
    }};

// Expected encoded message = (sig ^ 65537) mod N.
static const sigverify_rsa_buffer_t kRsaExpEncodedMessage = {
    .data = {
        0x05468728, 0x3ed0c5ca, 0x025d4fda, 0xcfa3e704, 0x507ce0d8, 0xecb616f6,
        0xa0a4a460, 0x3f0a377b, 0x05000420, 0x03040201, 0x86480165, 0x0d060960,
        0x00303130, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0x0001ffff,
    }};

// Sample key manager diversification data for testing.
static const keymgr_diversification_t kDiversification = {
    .salt = {0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0xf0f1f2f3,
             0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff},
    .version = 0,
};

// Test values for attestation key seeds.
static const uint32_t kSeedValues[3][kAttestationSeedWords] = {
    {
        0x70717273,
        0x74757677,
        0x78797a7b,
        0x7c7d7e7f,
        0x80818283,
        0x84858687,
        0x88898a8b,
        0x8c8d8e8f,
        0x90b1b2b3,
        0x94959697,
    },
    {
        0xa0a1a2a3,
        0xa4a5a6a7,
        0xa8a9aaab,
        0xacadaeaf,
        0xb0b1b2b3,
        0xb4b5b6b7,
        0xb8b9babb,
        0xbcbdbebf,
        0xc0b1b2b3,
        0xc4c5c6c7,
    },
    {
        0xd0d1d2d3,
        0xd4d5d6d7,
        0xd8d9dadb,
        0xdcdddedf,
        0xe0e1e2e3,
        0xe4e5e6e7,
        0xe8e9eaeb,
        0xecedeeef,
        0xf0b1b2b3,
        0xf4f5f6f7,
    },
};

// Message to sign for endorsement tests.
const char kEndorseTestMessage[] = "Test message.";
const size_t kEndorseTestMessageLen = sizeof(kEndorseTestMessage) - 1;

rom_error_t modexp_test(void) {
  sigverify_rsa_buffer_t encoded_message;
  RETURN_IF_ERROR(
      otbn_boot_sigverify_mod_exp(&kRsaKey, &kRsaSignature, &encoded_message));
  CHECK_ARRAYS_EQ(encoded_message.data, kRsaExpEncodedMessage.data,
                  ARRAYSIZE(kRsaExpEncodedMessage.data));
  return kErrorOk;
}

rom_error_t attestation_keygen_test(void) {
  // Check that key generations with different seeds result in different keys.
  attestation_public_key_t pk_uds;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                               kDiversification, &pk_uds));
  attestation_public_key_t pk_cdi0;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kCdi0AttestationKeySeed,
                                               kDiversification, &pk_cdi0));
  attestation_public_key_t pk_cdi1;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kCdi1AttestationKeySeed,
                                               kDiversification, &pk_cdi1));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds, (unsigned char *)&pk_cdi0,
                  sizeof(pk_uds));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds, (unsigned char *)&pk_cdi1,
                  sizeof(pk_uds));
  CHECK_ARRAYS_NE((unsigned char *)&pk_cdi0, (unsigned char *)&pk_cdi1,
                  sizeof(pk_uds));

  // Check that running the same key generation twice results in the same key.
  attestation_public_key_t pk_uds_again;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, kDiversification, &pk_uds_again));
  CHECK_ARRAYS_EQ((unsigned char *)&pk_uds_again, (unsigned char *)&pk_uds,
                  sizeof(pk_uds));

  // Check that key generations with different diversification result in
  // different keys.
  keymgr_diversification_t diversification_modified;
  memcpy(&diversification_modified, &kDiversification,
         sizeof(diversification_modified));
  diversification_modified.salt[0] ^= 1;
  attestation_public_key_t pk_uds_div;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, diversification_modified, &pk_uds_div));
  CHECK_ARRAYS_NE((unsigned char *)&pk_uds_div, (unsigned char *)&pk_uds,
                  sizeof(pk_uds));
  return kErrorOk;
}

rom_error_t attestation_advance_and_endorse_test(void) {
  // Generate and save the a keypair.
  attestation_public_key_t pk;
  RETURN_IF_ERROR(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                               kDiversification, &pk));
  RETURN_IF_ERROR(
      otbn_boot_attestation_key_save(kUdsAttestationKeySeed, kDiversification));

  // Advance keymgr to the next stage.
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey));
  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));

  // Run endorsement (should overwrite the key with randomness when done).
  hmac_digest_t digest;
  hmac_sha256(kEndorseTestMessage, kEndorseTestMessageLen, &digest);
  attestation_signature_t sig;
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // TODO: run an ECDSA signature verification here once we have code for that.
  // For now, just log the key and signature so we can check offline.
  LOG_INFO("x = 0x%08x%08x%08x%08x%08x%08x%08x%08x", pk.x[7], pk.x[6], pk.x[5],
           pk.x[4], pk.x[3], pk.x[2], pk.x[1], pk.x[0]);
  LOG_INFO("y = 0x%08x%08x%08x%08x%08x%08x%08x%08x", pk.y[7], pk.y[6], pk.y[5],
           pk.y[4], pk.y[3], pk.y[2], pk.y[1], pk.y[0]);
  LOG_INFO("digest = 0x%08x%08x%08x%08x%08x%08x%08x%08x", digest.digest[7],
           digest.digest[6], digest.digest[5], digest.digest[4],
           digest.digest[3], digest.digest[2], digest.digest[1],
           digest.digest[0]);
  LOG_INFO("Signature (expected valid):");
  LOG_INFO("r = 0x%08x%08x%08x%08x%08x%08x%08x%08x", sig.r[7], sig.r[6],
           sig.r[5], sig.r[4], sig.r[3], sig.r[2], sig.r[1], sig.r[0]);
  LOG_INFO("s = 0x%08x%08x%08x%08x%08x%08x%08x%08x", sig.s[7], sig.s[6],
           sig.s[5], sig.s[4], sig.s[3], sig.s[2], sig.s[1], sig.s[0]);

  // Run endorsement again (should not return an error, but should produce an
  // invalid signature).
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // TODO: run an ECDSA signature verification here once we have code for that.
  LOG_INFO("Signature (expected invalid):");
  LOG_INFO("r = 0x%08x%08x%08x%08x%08x%08x%08x%08x", sig.r[7], sig.r[6],
           sig.r[5], sig.r[4], sig.r[3], sig.r[2], sig.r[1], sig.r[0]);
  LOG_INFO("s = 0x%08x%08x%08x%08x%08x%08x%08x%08x", sig.s[7], sig.s[6],
           sig.s[5], sig.s[4], sig.s[3], sig.s[2], sig.s[1], sig.s[0]);

  return kErrorOk;
}

// N.B. This test will lock OTBN, so it needs to be the last test that runs.
rom_error_t attestation_save_clear_key_test(void) {
  // Save and then clear a private key.
  RETURN_IF_ERROR(
      otbn_boot_attestation_key_save(kUdsAttestationKeySeed, kDiversification));
  RETURN_IF_ERROR(otbn_boot_attestation_key_clear());

  // Save the private key again and check that endorsing succeeds.
  RETURN_IF_ERROR(
      otbn_boot_attestation_key_save(kUdsAttestationKeySeed, kDiversification));
  hmac_digest_t digest;
  hmac_sha256(kEndorseTestMessage, kEndorseTestMessageLen, &digest);
  attestation_signature_t sig;
  RETURN_IF_ERROR(otbn_boot_attestation_endorse(&digest, &sig));

  // Clear the key and check that endorsing now fails (it should even lock
  // OTBN).
  RETURN_IF_ERROR(otbn_boot_attestation_key_clear());
  hmac_sha256(kEndorseTestMessage, kEndorseTestMessageLen, &digest);
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

  EXECUTE_TEST(result, modexp_test);
  EXECUTE_TEST(result, attestation_keygen_test);
  EXECUTE_TEST(result, attestation_advance_and_endorse_test);
  EXECUTE_TEST(result, attestation_save_clear_key_test);

  return status_ok(result);
}
