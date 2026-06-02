// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/otbn_boot_services.h"

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/lib/sw/device/silicon_creator/attestation.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/dbg_print.h"

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
};

rom_error_t otbn_boot_app_load(void) { return sc_otbn_load_app(kOtbnAppBoot); }

rom_error_t otbn_boot_sigverify(const attestation_public_key_t *key,
                                const attestation_signature_t *sig,
                                const hmac_digest_t *digest,
                                uint32_t *recovered_r) {
  // Write the mode.
  uint32_t mode = kOtbnBootModeSigverify;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kOtbnBootModeWords, &mode, kOtbnVarBootMode));

  // Write the public key.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(kAttestationPublicKeyCoordWords,
                                              key->x, kOtbnVarBootX));
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(kAttestationPublicKeyCoordWords,
                                              key->y, kOtbnVarBootY));

  // Write the message digest.
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_dmem_write(kHmacDigestNumWords, digest->digest, kOtbnVarBootMsg));

  // Write the signature.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      kAttestationSignatureComponentWords, sig->r, kOtbnVarBootR));
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      kAttestationSignatureComponentWords, sig->s, kOtbnVarBootS));

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
  return sc_otbn_dmem_read(kAttestationSignatureComponentWords, kOtbnVarBootXr,
                           recovered_r);
}
