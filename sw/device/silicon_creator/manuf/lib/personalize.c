// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/manuf/keys/manuf_keys.h"

#include "otp_ctrl_regs.h"  // Generated.

enum {
  /**
   * RMA unlock token OTP offset.
   */
  kRmaUnlockTokenOffset =
      OTP_CTRL_PARAM_RMA_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET2_OFFSET,

  /**
   * RootKey sizes and offsets.
   *
   * The RootKey is stored in OTP, and is used to derive CreatorRootKey.
   */
  kRootKeyShareSizeInBytes = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE,
  kRootKeyShareSizeIn32BitWords = kRootKeyShareSizeInBytes / sizeof(uint32_t),
  kRootKeyShareSizeIn64BitWords = kRootKeyShareSizeInBytes / sizeof(uint64_t),
  kRootKeyOffsetShare0 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,
  kRootKeyOffsetShare1 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,

  /**
   * CreatorSeed and OwnerSeed sizes.
   *
   * Both seeds are stored in flash info pages. The CreatorSeed is used to
   * derive the CreatorRootKey, and also referred to as the `DiversificationKey`
   * in the "Identities and Root Keys" OpenTitan specification. The OwnerSeed is
   * used to derive the OwnerIntermediateKey, and is also referred to as the
   * `OwnerRootSecret` in the aforementioned spec.
   */
  kCreatorSeedSizeInBytes = 32,
  kCreatorSeedSizeInWords = kCreatorSeedSizeInBytes / sizeof(uint32_t),
  kOwnerSeedSizeInWords = kCreatorSeedSizeInWords,

  /**
   * Creator/Owner seed flash partition ID.
   */
  kSeedFlashInfoPartitionId = 0,

  /**
   * Creator/Owner seed flash bank ID.
   */
  kSeedFlashInfoBankId = 0,

  /**
   * CreatorSeed flash info page ID.
   */
  kCreatorSeedFlashInfoPageId = 1,

  /**
   * OwnerSeed flash info page ID.
   */
  kOwnerSeedFlashInfoPageId = 2,
};

static_assert(OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE ==
                  OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE,
              "Detected Root key share size mismatch");
static_assert(OTP_CTRL_PARAM_RMA_TOKEN_SIZE == 16,
              "RMA token is not 128 bits (i.e., one AES block), re-evaluate "
              "padding / AES mode. Additionally, update ujson struct "
              "definition for the wrapped RMA unlock token.");

// ECC curve to use with ECDH keygen.
static const ecc_curve_t kCurveP256 = {
    .curve_type = kEccCurveTypeNistP256,
    .domain_parameter =
        (ecc_domain_t){
            .p = (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
            .a = (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
            .b = (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
            .q = (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
            .gx = NULL,
            .gy = NULL,
            .cofactor = 0u,
            .checksum = 0u,
        },
};

// ECDH private key configuration.
static const crypto_key_config_t kEcdhPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeEcdh,
    .key_length = kP256ScalarBytes,
    .hw_backed = kHardenedBoolFalse,
    .diversification_hw_backed =
        (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
    .security_level = kSecurityLevelHigh,
};

// ECDH shared secret configuration.
static const crypto_key_config_t kRmaUnlockTokenAesKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesEcb,
    .key_length = kP256CoordBytes,
    .hw_backed = kHardenedBoolFalse,
    .diversification_hw_backed =
        (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
    .security_level = kSecurityLevelHigh,
};

/**
 * Generate ECDH keypair for use in generating an ephemeral AES encryption key
 * for exporting the RMA unlock token.
 *
 * @param[in,out] aes_key RMA unlock token AES encryption key buffer.
 * @param[out] wrapped_token Wrapped RMA unlock token struct that stores the
 *                           ECDH device public key and encrypted RMA token.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT static status_t gen_rma_unlock_token_aes_key(
    crypto_blinded_key_t *aes_key, wrapped_rma_unlock_token_t *wrapped_token) {
  // ECDH private key.
  uint32_t sk_device_keyblob[keyblob_num_words(kEcdhPrivateKeyConfig)];
  crypto_blinded_key_t sk_device = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(sk_device_keyblob),
      .keyblob = sk_device_keyblob,
      .checksum = 0,
  };

  // ECDH public key.
  ecc_public_key_t pk_device = {
      .x =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = kP256CoordWords * sizeof(uint32_t),
              .key = wrapped_token->ecc_pk_device_x,
          },
      .y =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = kP256CoordWords * sizeof(uint32_t),
              .key = wrapped_token->ecc_pk_device_y,
          },
  };

  TRY(otcrypto_ecdh_keygen(&kCurveP256, &sk_device, &pk_device));

  return otcrypto_ecdh(&sk_device, &kRmaUnlockTokenExportKeyPkHsm, &kCurveP256,
                       aes_key);
}

OT_WARN_UNUSED_RESULT
static status_t encrypt_rma_unlock_token(
    crypto_blinded_key_t *aes_key, wrapped_rma_unlock_token_t *wrapped_token) {
  // Construct IV, which since we are using ECB mode, is empty.
  crypto_uint8_buf_t iv = {
      .data = NULL,
      .len = 0,
  };

  // Construct plaintext buffer.
  crypto_const_uint8_buf_t plaintext = {
      .data = (const unsigned char *)wrapped_token->data,
      .len = kRmaUnlockTokenSizeInBytes,
  };

  // Construct ciphertext buffer. (No need for padding since RMA unlock token
  // is 128-bits already.)
  uint32_t ciphertext_data[kRmaUnlockTokenSizeInBytes];
  crypto_uint8_buf_t ciphertext = {
      .data = (unsigned char *)ciphertext_data,
      .len = kRmaUnlockTokenSizeInBytes,
  };

  // Run encryption and check the result.
  TRY(otcrypto_aes(aes_key, iv, kBlockCipherModeEcb, kAesOperationEncrypt,
                   plaintext, kAesPaddingNull, ciphertext));

  // Copy encrypted RMA unlock token to the output buffer.
  memcpy(wrapped_token->data, ciphertext.data, kRmaUnlockTokenSizeInBytes);

  return OK_STATUS();
}

/**
 * Performs sanity check of buffers holding a masked secret.
 *
 * @param share0 Share 0 buffer.
 * @param share1 Share 1 buffer.
 * @param len Number of 64bit words to sanity check.
 * @return OK_STATUS if share0 ^ share1 is not zero and if both shares don't
 * contain non-zero and non-all-FFs 64bit words.
 */
OT_WARN_UNUSED_RESULT
static status_t shares_check(uint64_t *share0, uint64_t *share1, size_t len) {
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |= share0[i] == share1[i];
    found_error |= share0[i] == UINT64_MAX || share0[i] == 0;
    found_error |= share1[i] == UINT64_MAX || share1[0] == 0;
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

/**
 * Checks if the SECRET2 OTP partition is in locked state.
 *
 * @param otp_ctrl OTP controller instance.
 * @param[out] is_locked Set to true if the SECRET2 partition is locked.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_partition_secret2_is_locked(const dif_otp_ctrl_t *otp_ctrl,
                                                bool *is_locked) {
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                      is_locked));
  return OK_STATUS();
}

/**
 * Writes a device-generated secret to a flash info page.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the target
 * flash info page.
 *
 * @param flash_state Flash controller instance.
 * @param page_id Region page index.
 * @param bank_id The required bank.
 * @param partition_id The partition index.
 * @param len The number of uint32_t words to program starting at the begining
 * of the target flash info page.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t flash_ctrl_secret_write(dif_flash_ctrl_state_t *flash_state,
                                        uint32_t page_id, uint32_t bank_id,
                                        uint32_t partition_id, size_t len) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint32_t seed[kCreatorSeedSizeInWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, seed, len));
  TRY(entropy_csrng_uninstantiate());

  uint32_t address = 0;
  TRY(flash_ctrl_testutils_info_region_scrambled_setup(
      flash_state, page_id, bank_id, partition_id, &address));

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash_state, address, partition_id, seed, kDifFlashCtrlPartitionTypeInfo,
      len));

  uint32_t seed_result[kCreatorSeedSizeInWords];
  TRY(flash_ctrl_testutils_read(flash_state, address, partition_id, seed_result,
                                kDifFlashCtrlPartitionTypeInfo, len,
                                /*delay=*/0));
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |=
        seed[i] == 0 || seed[i] == UINT32_MAX || seed[i] != seed_result[i];
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

/**
 * Hashes a lifecycle transition token to prepare it to be written to OTP.
 *
 * According to the Lifecycle Controller's specification:
 *
 * "All 128bit lock and unlock tokens are passed through a cryptographic one way
 * function in hardware before the life cycle controller compares them to the
 * provisioned values ...", and
 * "The employed one way function is a 128bit cSHAKE hash with the function name
 * “” and customization string “LC_CTRL”".
 *
 * @param raw_token The raw token to be hashed.
 * @param token_size The expected hashed token size in bytes.
 * @param[out] hashed_token The hashed token.
 * @return Result of the hash operation.
 */
OT_WARN_UNUSED_RESULT
static status_t hash_lc_transition_token(uint32_t *raw_token, size_t token_size,
                                         uint64_t *hashed_token) {
  crypto_const_uint8_buf_t input = {
      .data = (uint8_t *)raw_token,
      .len = token_size,
  };
  crypto_const_uint8_buf_t function_name_string = {
      .data = (uint8_t *)"",
      .len = 0,
  };
  crypto_const_uint8_buf_t customization_string = {
      .data = (uint8_t *)"LC_CTRL",
      .len = 7,
  };
  crypto_uint8_buf_t output = {
      .data = (uint8_t *)hashed_token,
      .len = token_size,
  };

  TRY(otcrypto_xof(input, kXofModeSha3Cshake128, function_name_string,
                   customization_string, token_size, &output));

  return OK_STATUS();
}

/**
 * Configures the RMA unlock token and Silicon Creator seed secret shares in the
 * SECRET2 OTP partition.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the SECRET2
 * OTP partition. The data needs to be programmed before the OTP SECRET2
 * partition is locked and when the device is in DEV, PROD, or PROD_END
 * lifecyle state.
 *
 * @param otp_ctrl OTP controller instance.
 * @param[out] rma_unlock_token RMA unlock token to export export from the chip.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_partition_secret2_configure(
    const dif_otp_ctrl_t *otp_ctrl,
    wrapped_rma_unlock_token_t *rma_unlock_token) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  // Generate and hash RMA unlock token.
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, rma_unlock_token->data,
                             kRmaUnlockTokenSizeIn32BitWords));
  TRY(entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));
  uint64_t hashed_rma_unlock_token[kRmaUnlockTokenSizeIn64BitWords];
  TRY(hash_lc_transition_token(rma_unlock_token->data,
                               kRmaUnlockTokenSizeInBytes,
                               hashed_rma_unlock_token));

  // Generate RootKey shares.
  uint64_t share0[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share0,
                             kRootKeyShareSizeIn32BitWords));
  TRY(entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  uint64_t share1[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share1,
                             kRootKeyShareSizeIn32BitWords));
  TRY(entropy_csrng_uninstantiate());

  TRY(shares_check(share0, share1, kRootKeyShareSizeIn64BitWords));

  // Provision RMA unlock token and RootKey shares into OTP.
  TRY(otp_ctrl_testutils_dai_write64(
      otp_ctrl, kDifOtpCtrlPartitionSecret2, kRmaUnlockTokenOffset,
      hashed_rma_unlock_token, kRmaUnlockTokenSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare0, share0,
                                     kRootKeyShareSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare1, share1,
                                     kRootKeyShareSizeIn64BitWords));

  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t manuf_personalize_device(dif_flash_ctrl_state_t *flash_state,
                                  const dif_lc_ctrl_t *lc_ctrl,
                                  const dif_otp_ctrl_t *otp_ctrl,
                                  manuf_provisioning_t *export_data) {
  // Check life cycle in either PROD, PROD_END, or DEV.
  TRY(lc_ctrl_testutils_operational_state_check(lc_ctrl));

  // TODO(#17393): check SECRET1 and HW_CFG OTP partitions are locked.

  // Skip if SECRET2 partition is locked. We won't be able to configure the
  // secret info flash page nor the OTP secrets if the OTP SECRET2 partition is
  // locked.
  bool is_locked;
  TRY(otp_partition_secret2_is_locked(otp_ctrl, &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Re-initialize the entropy complex in continous mode. This also configures
  // the entropy_src health checks in FIPS mode.
  TRY(entropy_complex_init());

  // Generate AES encryption key and IV for exporting the RMA unlock token.
  // AES key (i.e., ECDH shared secret).
  uint32_t aes_key_buf[keyblob_num_words(kRmaUnlockTokenAesKeyConfig)];
  crypto_blinded_key_t token_aes_key = {
      .config = kRmaUnlockTokenAesKeyConfig,
      .keyblob_length = sizeof(aes_key_buf),
      .keyblob = aes_key_buf,
  };
  TRY(gen_rma_unlock_token_aes_key(&token_aes_key,
                                   &export_data->wrapped_rma_unlock_token));

  // Provision secret Creator / Owner key seeds in flash.
  // Provision CreatorSeed into target flash info page.
  TRY(flash_ctrl_secret_write(flash_state, kCreatorSeedFlashInfoPageId,
                              kSeedFlashInfoBankId, kSeedFlashInfoPartitionId,
                              kCreatorSeedSizeInWords));
  // Provision preliminary OwnerSeed into target flash info page (with
  // expectation that SiliconOwner will rotate this value during ownership
  // transfer).
  TRY(flash_ctrl_secret_write(flash_state, kOwnerSeedFlashInfoPageId,
                              kSeedFlashInfoBankId, kSeedFlashInfoPartitionId,
                              kOwnerSeedSizeInWords));

  // Provision the OTP SECRET2 partition.
  TRY(otp_partition_secret2_configure(otp_ctrl,
                                      &export_data->wrapped_rma_unlock_token));

  // Encrypt the RMA unlock token with AES.
  TRY(encrypt_rma_unlock_token(&token_aes_key,
                               &export_data->wrapped_rma_unlock_token));

  return OK_STATUS();
}

status_t manuf_personalize_device_check(const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(otp_partition_secret2_is_locked(otp_ctrl, &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
