// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include "otbn_regs.h"  // Generated.

static_assert(kAttestationSeedWords <= 16,
              "Additional attestation seed needs must be <= 516 bits.");

OTBN_DECLARE_APP_SYMBOLS(boot);        // The OTBN boot-services app.
OTBN_DECLARE_SYMBOL_ADDR(boot, mode);  // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(boot, msg);   // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(boot, x);     // ECDSA public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(boot, y);     // ECDSA public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(boot, r);     // ECDSA signature component r.
OTBN_DECLARE_SYMBOL_ADDR(boot, s);     // ECDSA signature component s.
OTBN_DECLARE_SYMBOL_ADDR(boot, x_r);   // ECDSA verification result.
OTBN_DECLARE_SYMBOL_ADDR(boot, ok);    // ECDSA verification status.
OTBN_DECLARE_SYMBOL_ADDR(
    boot, attestation_additional_seed);  // Additional seed for ECDSA keygen.

static const sc_otbn_app_t kOtbnAppBoot = OTBN_APP_T_INIT(boot);
static const sc_otbn_addr_t kOtbnVarBootMode = OTBN_ADDR_T_INIT(boot, mode);
static const sc_otbn_addr_t kOtbnVarBootMsg = OTBN_ADDR_T_INIT(boot, msg);
static const sc_otbn_addr_t kOtbnVarBootX = OTBN_ADDR_T_INIT(boot, x);
static const sc_otbn_addr_t kOtbnVarBootY = OTBN_ADDR_T_INIT(boot, y);
static const sc_otbn_addr_t kOtbnVarBootR = OTBN_ADDR_T_INIT(boot, r);
static const sc_otbn_addr_t kOtbnVarBootS = OTBN_ADDR_T_INIT(boot, s);
static const sc_otbn_addr_t kOtbnVarBootXr = OTBN_ADDR_T_INIT(boot, x_r);
static const sc_otbn_addr_t kOtbnVarBootOk = OTBN_ADDR_T_INIT(boot, ok);
static const sc_otbn_addr_t kOtbnVarBootAttestationAdditionalSeed =
    OTBN_ADDR_T_INIT(boot, attestation_additional_seed);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnBootModeWords = 1,
  /*
   * Mode to run signature verification.
   *
   * Value taken from `boot.s`.
   */
  kOtbnBootModeSigverify = 0x7d3,
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
      ((kAttestationSeedWords + kScOtbnWideWordNumWords - 1) /
       kScOtbnWideWordNumWords) *
      kScOtbnWideWordNumWords,
};

OT_WARN_UNUSED_RESULT
static rom_error_t load_attestation_keygen_seed(
    attestation_key_seed_t additional_seed, uint32_t *seed) {
  // Read seed from flash info page.
  uint32_t seed_flash_offset = 0 + (additional_seed * kAttestationSeedBytes);
  rom_error_t err =
      flash_ctrl_info_read(&kFlashCtrlInfoPageAttestationKeySeeds,
                           seed_flash_offset, kAttestationSeedWords, seed);

  if (err != kErrorOk) {
    flash_ctrl_error_code_t flash_ctrl_err_code;
    flash_ctrl_error_code_get(&flash_ctrl_err_code);
    if (flash_ctrl_err_code.rd_err) {
      // If we encountered a read error, this means the attestation seed page
      // has not been provisioned yet. In this case, we erase the page and
      // continue, which will simply result in generating an invalid identity.
      dbg_printf(
          "Warning: Attestation key seed flash info page not provisioned. "
          "Erasing page to format.\r\n");
      HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(
          &kFlashCtrlInfoPageAttestationKeySeeds, kFlashCtrlEraseTypePage));
      return kErrorOk;
    }
    return err;
  }

  return kErrorOk;
}

rom_error_t otbn_boot_app_load(void) { return sc_otbn_load_app(kOtbnAppBoot); }

rom_error_t otbn_boot_attestation_keygen(
    attestation_key_seed_t additional_seed, sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification,
    ecdsa_p256_public_key_t *public_key) {
  // Trigger key manager to sideload the attestation key into OTBN.
  HARDENED_RETURN_IF_ERROR(
      sc_keymgr_generate_key_otbn(key_type, diversification));

  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationKeygen;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Load the additional seed from flash info.
  uint32_t seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(additional_seed, seed));

  // Write the additional seed to OTBN DMEM.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      kAttestationSeedWords, seed, kOtbnVarBootAttestationAdditionalSeed));
  // Pad remaining DMEM field with zeros to prevent a DMEM integrity error
  // (since data is aligned to 256-bit words).
  uint32_t zero_buf[kOtbnAttestationSeedBufferWords - kAttestationSeedWords] = {
      0};
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      ARRAYSIZE(zero_buf), zero_buf,
      kOtbnVarBootAttestationAdditionalSeed + kAttestationSeedBytes));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kScOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Retrieve the public key.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(kEcdsaP256PublicKeyCoordWords,
                                             kOtbnVarBootX, public_key->x));
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(kEcdsaP256PublicKeyCoordWords,
                                             kOtbnVarBootY, public_key->y));

  return kErrorOk;
}

rom_error_t otbn_boot_attestation_key_save(
    attestation_key_seed_t additional_seed, sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification) {
  // Trigger key manager to sideload the attestation key into OTBN.
  HARDENED_RETURN_IF_ERROR(
      sc_keymgr_generate_key_otbn(key_type, diversification));

  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationKeySave;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Load the additional seed from flash info.
  uint32_t seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(additional_seed, seed));
  // Pad remaining DMEM field with zeros to prevent a DMEM integrity error
  // (since data is aligned to 256-bit words).
  uint32_t zero_buf[kOtbnAttestationSeedBufferWords - kAttestationSeedWords] = {
      0};
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      ARRAYSIZE(zero_buf), zero_buf,
      kOtbnVarBootAttestationAdditionalSeed + kAttestationSeedBytes));

  // Write the additional seed to OTBN DMEM.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      kAttestationSeedWords, seed, kOtbnVarBootAttestationAdditionalSeed));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kScOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  return kErrorOk;
}

rom_error_t otbn_boot_attestation_key_clear(void) {
  // Trigger a full DMEM wipe.
  RETURN_IF_ERROR(sc_otbn_dmem_sec_wipe());
  HARDENED_RETURN_IF_ERROR(sc_otbn_busy_wait_for_done());

  // Re-load the data portion of the boot services app. This is like a
  // stripped-down version of `sc_otbn_load_app`, where we skip the IMEM.
  if (kOtbnAppBoot.dmem_data_end < kOtbnAppBoot.dmem_data_start) {
    return kErrorOtbnInvalidArgument;
  }
  HARDENED_CHECK_GE(kOtbnAppBoot.dmem_data_end, kOtbnAppBoot.dmem_data_start);
  const size_t data_num_words =
      (size_t)(kOtbnAppBoot.dmem_data_end - kOtbnAppBoot.dmem_data_start);
  if (data_num_words > 0) {
    HARDENED_RETURN_IF_ERROR(
        sc_otbn_dmem_write(data_num_words, kOtbnAppBoot.dmem_data_start,
                           kOtbnAppBoot.dmem_data_start_addr));
  }
  return kErrorOk;
}

rom_error_t otbn_boot_attestation_endorse(const hmac_digest_t *digest,
                                          ecdsa_p256_signature_t *sig) {
  // Write the mode.
  uint32_t mode = kOtbnBootModeAttestationEndorse;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Write the message digest.
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kHmacDigestNumWords, digest->digest, kOtbnVarBootMsg));

  // Run the OTBN program (blocks until OTBN is done).
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kScOtbnSecMmioExecute);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Retrieve the signature (in two parts, r and s).
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(kEcdsaP256SignatureComponentWords,
                                             kOtbnVarBootR, sig->r));
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(kEcdsaP256SignatureComponentWords,
                                             kOtbnVarBootS, sig->s));

  return kErrorOk;
}

rom_error_t otbn_boot_sigverify(const ecdsa_p256_public_key_t *key,
                                const ecdsa_p256_signature_t *sig,
                                const hmac_digest_t *digest,
                                uint32_t *recovered_r) {
  // Write the mode.
  uint32_t mode = kOtbnBootModeSigverify;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Write the public key.
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kEcdsaP256PublicKeyCoordWords, key->x, kOtbnVarBootX));
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kEcdsaP256PublicKeyCoordWords, key->y, kOtbnVarBootY));

  // Write the message digest.
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kHmacDigestNumWords, digest->digest, kOtbnVarBootMsg));

  // Write the signature.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(kEcdsaP256SignatureComponentWords,
                                              sig->r, kOtbnVarBootR));
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(kEcdsaP256SignatureComponentWords,
                                              sig->s, kOtbnVarBootS));

  // Start the OTBN routine.
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kScOtbnSecMmioExecute);

  // Check if the signature passed basic checks.
  uint32_t ok;
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(1, kOtbnVarBootOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return kErrorSigverifyBadEcdsaSignature;
  }

  // Read the status value again as an extra hardening measure.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_read(1, kOtbnVarBootOk, &ok));
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // TODO(#20023): Check the instruction count register (see `mod_exp_otbn`).

  // Read the recovered `r` value from DMEM.
  return sc_otbn_dmem_read(kEcdsaP256SignatureComponentWords, kOtbnVarBootXr,
                           recovered_r);
}
