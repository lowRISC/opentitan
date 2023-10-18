// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/manuf/keys/manuf_keys.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/lib/util.h"

#include "otp_ctrl_regs.h"  // Generated.

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
            .p = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .a = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .b = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .q = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
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
    .security_level = kSecurityLevelHigh,
};

// ECDH shared secret configuration.
static const crypto_key_config_t kRmaUnlockTokenAesKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesEcb,
    .key_length = kP256CoordBytes,
    .hw_backed = kHardenedBoolFalse,
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
  crypto_word32_buf_t iv = {
      .data = NULL,
      .len = 0,
  };

  // Construct plaintext buffer.
  crypto_const_byte_buf_t plaintext = {
      .data = (const unsigned char *)wrapped_token->data,
      .len = kRmaUnlockTokenSizeInBytes,
  };

  // Construct ciphertext buffer. (No need for padding since RMA unlock token
  // is 128-bits already.)
  uint32_t ciphertext_data[kRmaUnlockTokenSizeInBytes];
  crypto_byte_buf_t ciphertext = {
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
 * Writes a device-generated secret to a flash info page.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the target
 * flash info page.
 *
 * @param flash_state Flash controller instance.
 * @param field Info flash field location information.
 * @param len The number of uint32_t words to program starting at the begining
 * of the target flash info page.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t flash_ctrl_secret_write(dif_flash_ctrl_state_t *flash_state,
                                        flash_info_field_t field, size_t len) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint32_t seed[kFlashInfoKeySeedSizeIn32BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, seed, len,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_uninstantiate());

  uint32_t address = 0;
  TRY(flash_ctrl_testutils_info_region_scrambled_setup(
      flash_state, field.page, field.bank, field.partition, &address));

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash_state, address, field.partition, seed,
      kDifFlashCtrlPartitionTypeInfo, len));

  uint32_t seed_result[kFlashInfoKeySeedSizeIn32BitWords];
  TRY(flash_ctrl_testutils_read(flash_state, address, field.partition,
                                seed_result, kDifFlashCtrlPartitionTypeInfo,
                                len,
                                /*delay=*/0));
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |=
        seed[i] == 0 || seed[i] == UINT32_MAX || seed[i] != seed_result[i];
  }
  return found_error ? INTERNAL() : OK_STATUS();
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
                             kRmaUnlockTokenSizeIn32BitWords,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));
  uint64_t hashed_rma_unlock_token[kRmaUnlockTokenSizeIn64BitWords];
  TRY(manuf_util_hash_lc_transition_token(rma_unlock_token->data,
                                          kRmaUnlockTokenSizeInBytes,
                                          hashed_rma_unlock_token));

  // Generate RootKey shares.
  uint64_t share0[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share0,
                             kRootKeyShareSizeIn32BitWords,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  uint64_t share1[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share1,
                             kRootKeyShareSizeIn32BitWords,
                             /*fips_check*/ kHardenedBoolTrue));
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

status_t manuf_personalize_device_secrets(dif_flash_ctrl_state_t *flash_state,
                                          const dif_lc_ctrl_t *lc_ctrl,
                                          const dif_otp_ctrl_t *otp_ctrl,
                                          manuf_perso_data_out_t *export_data) {
  // Check life cycle in either PROD, PROD_END, or DEV.
  TRY(lc_ctrl_testutils_operational_state_check(lc_ctrl));

  // Skip provisioning of SECRET1 OTP partition if already done.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Check the SECRET1 partition is locked. Flash scrambling seeds must be
  // provisioned before the keymgr seeds can be written to flash info pages, as
  // these pages must be scrambled.
  //
  // Note: for SECRET1 partition to be provisioned, the HW_CFG partition must
  // have been provisioned, and the CSRNG SW interface should have been enabled,
  // so no need to check again here.
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  if (!is_locked) {
    return INTERNAL();
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
  TRY(flash_ctrl_secret_write(flash_state, kFlashInfoFieldCreatorSeed,
                              kFlashInfoKeySeedSizeIn32BitWords));
  // Provision preliminary OwnerSeed into target flash info page (with
  // expectation that SiliconOwner will rotate this value during ownership
  // transfer).
  TRY(flash_ctrl_secret_write(flash_state, kFlashInfoFieldOwnerSeed,
                              kFlashInfoKeySeedSizeIn32BitWords));

  // Provision the OTP SECRET2 partition.
  TRY(otp_partition_secret2_configure(otp_ctrl,
                                      &export_data->wrapped_rma_unlock_token));

  // Encrypt the RMA unlock token with AES.
  TRY(encrypt_rma_unlock_token(&token_aes_key,
                               &export_data->wrapped_rma_unlock_token));

  return OK_STATUS();
}

OT_WARN_UNUSED_RESULT
static status_t otp_secret_write(const dif_otp_ctrl_t *otp_ctrl,
                                 uint32_t offset, size_t len) {
  enum {
    kBufferSize = 4,
  };
  if (len > kBufferSize) {
    return INTERNAL();
  }

  TRY(entropy_csrng_reseed(/*disable_trng_inpu=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  size_t len_in_32bit_words = len * 2;
  uint64_t data[kBufferSize];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)data,
                             len_in_32bit_words,
                             /*fips_check=*/kHardenedBoolTrue));

  bool found_error = false;
  uint64_t prev_val = 0;
  for (size_t i = 0; i < len; ++i) {
    found_error |= data[i] == 0 || data[i] == UINT64_MAX || data[i] == prev_val;
    prev_val = data[i];
  }
  if (found_error) {
    return INTERNAL();
  }

  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                     offset, data, len));
  return OK_STATUS();
}

status_t manuf_personalize_device_secrets_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}

status_t manuf_personalize_device_secret1(const dif_lc_ctrl_t *lc_ctrl,
                                          const dif_otp_ctrl_t *otp_ctrl) {
  // Skip provisioning of SECRET1 OTP partition if already done.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Check that the HW_CFG OTP partition has been locked (and is activated).
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                      &is_locked));
  if (!is_locked) {
    return INTERNAL();
  }

  // Check that the CSRNG SW application interface is enabled in the HW_CFG
  // partition, as we cannot provision SECRET1 without access to the CSRNG.
  uint32_t otp_hw_cfg_settings;
  TRY(otp_ctrl_testutils_dai_read32(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                    kHwCfgEnSramIfetchOffset,
                                    &otp_hw_cfg_settings));
  uint32_t csrng_sw_app_read =
      bitfield_field32_read(otp_hw_cfg_settings, kCsrngAppRead);
  if (csrng_sw_app_read != kMultiBitBool8True) {
    return INTERNAL();
  }

  TRY(entropy_complex_init());
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  TRY(otp_secret_write(otp_ctrl, kSecret1FlashAddrKeySeedOffset,
                       kSecret1FlashAddrKeySeed64BitWords));
  TRY(otp_secret_write(otp_ctrl, kSecret1FlashDataKeySeedOffset,
                       kSecret1FlashDataKeySeed64BitWords));
  TRY(otp_secret_write(otp_ctrl, kSecret1SramDataKeySeedOffset,
                       kSecret1SramDataKeySeed64Bitwords));

  TRY(entropy_csrng_uninstantiate());
  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t manuf_personalize_device_secret1_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
