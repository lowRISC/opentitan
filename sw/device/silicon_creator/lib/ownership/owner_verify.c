// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"

#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"

// A version of spx_verify that is tailored to ROM_EXT use cases.
// In particular:
//   - We don't care about the OTP setting for SPX+ in the ROM_EXT.
//   - We don't care about flash_exec in the ROM_EXT.
//   - We have a different series of algorithm identifier values to accommodate
//     hybrid signature schemes.
OT_WARN_UNUSED_RESULT
static rom_error_t owner_spx_verify(
    uint32_t key_alg, const sigverify_spx_key_t *key,
    const sigverify_spx_signature_t *signature, const void *msg_prefix_1,
    size_t msg_prefix_1_len, const void *msg_prefix_2, size_t msg_prefix_2_len,
    const void *msg, size_t msg_len, hmac_digest_t digest) {
  if (signature == NULL) {
    return kErrorSigverifySpxNotFound;
  }
  /*
   * Shares for producing kErrorOk if SPHINCS+ verification succeeds.  The first
   * three shares are generated using the `sparse-fsm-encode` script while the
   * last share is
   * `kErrorOk ^ shares[0] ^ ... ^ shares[2]`.
   *
   * Encoding generated with:
   * $ ./util/design/sparse-fsm-encode.py -d 5 -m 3 -n 32 \
   *     -s 1069420 --language=c
   *
   * Minimum Hamming distance: 14
   * Maximum Hamming distance: 20
   * Minimum Hamming weight: 14
   * Maximum Hamming weight: 16
   */

  const uint32_t shares[] = {
      0x11deb806,
      0x06457f69,
      0x647f10c4,
      0x73e4d092,
  };

  // If the key_alg is one of the hybrid algorithm, locally re-categorize as
  // an SPX+ algorithm so we can call the underlying `spx_verify` function
  // correctly.
  key_alg &= ~(uint32_t)kOwnershipKeyAlgCategoryMask;
  key_alg |= (uint32_t)kOwnershipKeyAlgCategorySpx;

  sigverify_spx_root_t actual_root;
  sigverify_spx_root_t expected_root;
  spx_public_key_root(key->data, expected_root.data);
  uint32_t i;
  for (i = 0; launder32(i) < kSigverifySpxRootNumWords; ++i) {
    expected_root.data[i] ^= shares[i];
  }

  switch (key_alg) {
    case kOwnershipKeyAlgSpxPure:
      HARDENED_RETURN_IF_ERROR(spx_verify(
          signature->data, kSpxVerifyPureDomainSep, kSpxVerifyPureDomainSepSize,
          msg_prefix_1, msg_prefix_1_len, msg_prefix_2, msg_prefix_2_len, msg,
          msg_len, key->data, actual_root.data));
      break;

    case kOwnershipKeyAlgSpxPrehash:
      util_reverse_bytes(digest.digest, sizeof(digest.digest));
      HARDENED_RETURN_IF_ERROR(
          spx_verify(signature->data, kSpxVerifyPrehashDomainSep,
                     kSpxVerifyPrehashDomainSepSize,
                     /*msg_prefix_2=*/NULL, /*msg_prefix_2_len=*/0,
                     /*msg_prefix_3=*/NULL, /*msg_prefix_3_len=*/0,
                     (unsigned char *)digest.digest, sizeof(digest.digest),
                     key->data, actual_root.data));
      break;
    default:
      return kErrorSigverifyBadSpxConfig;
  }
  uint32_t result = 0;
  uint32_t diff = 0;
  for (--i; launder32(i) < kSigverifySpxRootNumWords; --i) {
    uint32_t val = expected_root.data[i] ^ actual_root.data[i];
    diff |= val ^ shares[i];
    diff |= ~diff + 1;          // Set upper bits to 1 if not 0, no change o/w.
    diff |= ~(diff >> 31) + 1;  // Set all 1s if MSB is set, no change o/w.
    result ^= val;
    result |= diff;
  }
  HARDENED_CHECK_EQ(i, SIZE_MAX);
  if (result != kErrorOk) {
    return kErrorSigverifyBadSpxSignature;
  }
  return result;
}

rom_error_t owner_verify(uint32_t key_alg, const owner_keydata_t *key,
                         const ecdsa_p256_signature_t *ecdsa_sig,
                         const sigverify_spx_signature_t *spx_sig,
                         const void *msg_prefix_1, size_t msg_prefix_1_len,
                         const void *msg_prefix_2, size_t msg_prefix_2_len,
                         const void *msg, size_t msg_len,
                         const hmac_digest_t *digest, uint32_t *flash_exec) {
  uint32_t ec_flash_exec = 0;
  uint32_t category = key_alg & kOwnershipKeyAlgCategoryMask;
  rom_error_t ecdsa = kErrorOwnershipInvalidAlgorithm;
  rom_error_t spx = kErrorOwnershipInvalidAlgorithm;

  // Start an ECDSA verify on OTBN (if requested by the key_alg).
  if (category == kOwnershipKeyAlgCategoryEcdsa ||
      category == kOwnershipKeyAlgCategoryHybrid) {
    HARDENED_RETURN_IF_ERROR(sigverify_ecdsa_p256_start(
        ecdsa_sig,
        category == kOwnershipKeyAlgCategoryHybrid ? &key->hybrid.ecdsa
                                                   : &key->ecdsa,
        digest));
  }

  // While ECDSA verify is running in OTBN, compute the SPX verify on Ibex.
  if (category == kOwnershipKeyAlgCategorySpx ||
      category == kOwnershipKeyAlgCategoryHybrid) {
    spx = owner_spx_verify(
        key_alg,
        category == kOwnershipKeyAlgCategoryHybrid ? &key->hybrid.spx
                                                   : &key->spx,
        spx_sig, msg_prefix_1, msg_prefix_1_len, msg_prefix_2, msg_prefix_2_len,
        msg, msg_len, *digest);
  } else {
    HARDENED_CHECK_EQ(category, kOwnershipKeyAlgCategoryEcdsa);
    spx = kErrorOk;
  }

  // ECDSA should be finished.  Poll for completeion and get the result.
  if (category == kOwnershipKeyAlgCategoryEcdsa ||
      category == kOwnershipKeyAlgCategoryHybrid) {
    ecdsa = sigverify_ecdsa_p256_finish(ecdsa_sig, &ec_flash_exec);
  } else {
    HARDENED_CHECK_EQ(category, kOwnershipKeyAlgCategorySpx);
    ecdsa = kErrorOk;
  }
  HARDENED_RETURN_IF_ERROR(spx);
  HARDENED_RETURN_IF_ERROR(ecdsa);
  if (flash_exec) {
    *flash_exec = ec_flash_exec;
  }
  // Both values should be kErrorOk.  Mix them and return the result.
  return (rom_error_t)((spx + ecdsa) >> 1);
}
