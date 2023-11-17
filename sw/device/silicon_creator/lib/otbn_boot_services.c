// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"

static_assert(kAttestationSeedWords <= 16,
              "Additional attestation seed needs must be <= 516 bits.");

OTBN_DECLARE_APP_SYMBOLS(boot);             // The OTBN boot-services app.
OTBN_DECLARE_SYMBOL_ADDR(boot, mode);       // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(boot, rsa_mod);    // RSA modulus.
OTBN_DECLARE_SYMBOL_ADDR(boot, rsa_m0inv);  // RSA Montgomery constant.
OTBN_DECLARE_SYMBOL_ADDR(boot, rsa_inout);  // RSA input/output buffer.
OTBN_DECLARE_SYMBOL_ADDR(boot, msg);        // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(boot, x);          // ECDSA public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(boot, y);          // ECDSA public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(boot, r);          // ECDSA signature component r.
OTBN_DECLARE_SYMBOL_ADDR(boot, s);          // ECDSA signature component s.
OTBN_DECLARE_SYMBOL_ADDR(
    boot, attestation_additional_seed);  // Additional seed for ECDSA keygen.

static const otbn_app_t kOtbnAppBoot = OTBN_APP_T_INIT(boot);
static const otbn_addr_t kOtbnVarBootMode = OTBN_ADDR_T_INIT(boot, mode);
static const otbn_addr_t kOtbnVarBootRsaMod = OTBN_ADDR_T_INIT(boot, rsa_mod);
static const otbn_addr_t kOtbnVarBootRsaM0inv =
    OTBN_ADDR_T_INIT(boot, rsa_m0inv);
static const otbn_addr_t kOtbnVarBootRsaInout =
    OTBN_ADDR_T_INIT(boot, rsa_inout);
static const otbn_addr_t kOtbnVarBootMsg = OTBN_ADDR_T_INIT(boot, msg);
static const otbn_addr_t kOtbnVarBootX = OTBN_ADDR_T_INIT(boot, x);
static const otbn_addr_t kOtbnVarBootY = OTBN_ADDR_T_INIT(boot, y);
static const otbn_addr_t kOtbnVarBootR = OTBN_ADDR_T_INIT(boot, r);
static const otbn_addr_t kOtbnVarBootS = OTBN_ADDR_T_INIT(boot, s);
static const otbn_addr_t kOtbnVarBootAttestationAdditionalSeed =
    OTBN_ADDR_T_INIT(boot, attestation_additional_seed);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnBootModeWords = 1,
  /*
   * Mode to run RSA modular exponentiation.
   *
   * Value taken from `boot.s`.
   */
  kOtbnBootModeSecBootModexp = 0x7d3,
  /*
   * Mode to generate an attestation keypair.
   *
   * Value taken from `boot.s`.
   */
  kOtbnBootModeAttestationKeygen = 0x2bf,
  /*
   * Mode to endorse a message with a saved private key.
   *
   * Value taken from `boot.s`.
   */
  kOtbnBootModeAttestationEndorse = 0x5e8,
  /*
   * Mode to save an attesation private key.
   *
   * Value taken from `boot.s`.
   */
  kOtbnBootModeAttestationKeySave = 0x64d,
  /* Size of the OTBN attestation seed buffer in 32-bit words (rounding the
     attestation seed size up to the next OTBN wide word). */
  kOtbnAttestationSeedBufferWords =
      ((kAttestationSeedWords + kOtbnWideWordNumWords - 1) /
       kOtbnWideWordNumWords) *
      kOtbnWideWordNumWords,
};

OT_WARN_UNUSED_RESULT
static rom_error_t load_attestation_keygen_seed(
    attestation_key_seed_t additional_seed, uint32_t *seed) {
  // Set flash page configuration and permissions.
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageAttestationKeySeeds,
                            (flash_ctrl_perms_t){
                                .read = kMultiBitBool4True,
                                .write = kMultiBitBool4False,
                                .erase = kMultiBitBool4False,
                            });
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageAttestationKeySeeds,
                          (flash_ctrl_cfg_t){
                              .scrambling = kMultiBitBool4True,
                              .ecc = kMultiBitBool4True,
                              .he = kMultiBitBool4False,
                          });

  // Read seed from flash info page.
  uint32_t seed_flash_offset = 0 + (additional_seed * kAttestationSeedWords);
  HARDENED_RETURN_IF_ERROR(
      flash_ctrl_info_read(&kFlashCtrlInfoPageAttestationKeySeeds,
                           seed_flash_offset, kAttestationSeedWords, seed));

  return kErrorOk;
}

rom_error_t otbn_boot_app_load(void) { return otbn_load_app(kOtbnAppBoot); }

rom_error_t otbn_boot_attestation_keygen(
    attestation_key_seed_t additional_seed,
    keymgr_diversification_t diversification,
    attestation_public_key_t *public_key) {
  // Trigger key manager to sideload the attestation key into OTBN.
  HARDENED_RETURN_IF_ERROR(
      keymgr_generate_attestation_key_otbn(diversification));

  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationKeygen;
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Load the additional seed from flash info.
  uint32_t seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(additional_seed, seed));

  // Write the additional seed to OTBN DMEM.
  HARDENED_RETURN_IF_ERROR(otbn_dmem_write(
      kAttestationSeedWords, seed, kOtbnVarBootAttestationAdditionalSeed));
  // Pad remaining DMEM field with zeros to prevent a DMEM integrity error
  // (since data is aligned to 256-bit words).
  uint32_t zero_buf[kOtbnAttestationSeedBufferWords - kAttestationSeedWords] = {
      0};
  HARDENED_RETURN_IF_ERROR(otbn_dmem_write(
      ARRAYSIZE(zero_buf), zero_buf,
      kOtbnVarBootAttestationAdditionalSeed + kAttestationSeedBytes));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Retrieve the public key.
  HARDENED_RETURN_IF_ERROR(otbn_dmem_read(kAttestationPublicKeyCoordWords,
                                          kOtbnVarBootX, public_key->x));
  HARDENED_RETURN_IF_ERROR(otbn_dmem_read(kAttestationPublicKeyCoordWords,
                                          kOtbnVarBootY, public_key->y));

  return kErrorOk;
}

rom_error_t otbn_boot_attestation_key_save(
    attestation_key_seed_t additional_seed,
    keymgr_diversification_t diversification) {
  // Trigger key manager to sideload the attestation key into OTBN.
  HARDENED_RETURN_IF_ERROR(
      keymgr_generate_attestation_key_otbn(diversification));

  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationKeySave;
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Load the additional seed from flash info.
  uint32_t seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(additional_seed, seed));
  // Pad remaining DMEM field with zeros to prevent a DMEM integrity error
  // (since data is aligned to 256-bit words).
  uint32_t zero_buf[kOtbnAttestationSeedBufferWords - kAttestationSeedWords] = {
      0};
  HARDENED_RETURN_IF_ERROR(otbn_dmem_write(
      ARRAYSIZE(zero_buf), zero_buf,
      kOtbnVarBootAttestationAdditionalSeed + kAttestationSeedBytes));

  // Write the additional seed to OTBN DMEM.
  HARDENED_RETURN_IF_ERROR(otbn_dmem_write(
      kAttestationSeedWords, seed, kOtbnVarBootAttestationAdditionalSeed));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  return kErrorOk;
}

rom_error_t otbn_boot_attestation_key_clear(void) {
  return otbn_dmem_sec_wipe();
}

rom_error_t otbn_boot_attestation_endorse(const hmac_digest_t *digest,
                                          attestation_signature_t *sig) {
  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationEndorse;
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Write the message digest.
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kHmacDigestNumWords, digest->digest, kOtbnVarBootMsg));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Retrieve the signature (in two parts, r and s).
  size_t half_num_words = kAttestationSignatureWords / 2;
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_read(half_num_words, kOtbnVarBootR, sig->r));
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_read(half_num_words, kOtbnVarBootS, sig->s));

  return kErrorOk;
}

rom_error_t otbn_boot_sigverify_mod_exp(const sigverify_rsa_key_t *key,
                                        const sigverify_rsa_buffer_t *sig,
                                        sigverify_rsa_buffer_t *result) {
  // Set the modulus (n).
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kSigVerifyRsaNumWords, key->n.data, kOtbnVarBootRsaMod));

  // Set the encoded message.
  HARDENED_RETURN_IF_ERROR(
      otbn_dmem_write(kSigVerifyRsaNumWords, sig->data, kOtbnVarBootRsaInout));

  // Set the precomputed constant m0_inv.
  HARDENED_RETURN_IF_ERROR(otbn_dmem_write(kOtbnWideWordNumWords, key->n0_inv,
                                           kOtbnVarBootRsaM0inv));

  // Start the OTBN routine.
  HARDENED_RETURN_IF_ERROR(otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Read recovered message out of OTBN dmem.
  return otbn_dmem_read(kSigVerifyRsaNumWords, kOtbnVarBootRsaInout,
                        result->data);
}
