// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sigverify.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_mod_exp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Returns the key with the given ID.
 *
 * @param key_id A key ID.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
static rom_error_t sigverify_rsa_key_get(uint32_t key_id,
                                         const sigverify_rsa_key_t **key) {
  for (size_t i = 0; i < kSigVerifyNumRsaKeys; ++i) {
    const sigverify_rsa_key_t *cand_key = &kSigVerifyRsaKeys[i];
    if (sigverify_rsa_key_id_get(cand_key) == key_id) {
      *key = cand_key;
      return kErrorOk;
    }
  }
  return kErrorSigverifyInvalidArgument;
}

/**
 * Checks the padding and the digest of an EMSA-PKCS1-v1_5 encoded message.
 *
 * EMSA-PKCS1-v1_5 is described in Section 9.2 of PKCS #1: RSA Cryptography
 * Specifications Version 2.2 (https://tools.ietf.org/html/rfc8017#section-9.2).
 * In PKCS#1, sequences are indexed from the leftmost byte and the first byte is
 * the most significant byte. An encoded message EM is an octet string of the
 * form:
 *    EM = 0x00 || 0x01 || PS || 0x00 || T, where
 * PS is a byte string of `0xff`s, T is the DER encoding of ASN.1 value of type
 * DigestInfo that contains the digest algorithm and the digest, and || denotes
 * concatenation. For SHA-256:
 *    T = (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || H,
 * where H is the digest.
 *
 * This function checks the padding and the digest of an encoded message as
 * described in PKCS#1 but works on little-endian buffers.
 *
 * @param enc_msg An encoded message, little-endian.
 * @param act_digest Actual digest of the message being verified, little-endian.
 * @return Result of the operation.
 */
static rom_error_t sigverify_padding_and_digest_check(
    const sigverify_rsa_buffer_t *enc_msg, const hmac_digest_t *act_digest) {
  const uint32_t *enc_msg_ptr = enc_msg->data;

  if (memcmp(enc_msg_ptr, act_digest->digest, sizeof(act_digest->digest)) !=
      0) {
    return kErrorSigverifyInvalidArgument;
  }
  enc_msg_ptr += ARRAYSIZE(act_digest->digest);

  // Note: This also includes the zero byte right before PS.
  static const uint32_t kEncodedSha256[] = {
      0x05000420, 0x03040201, 0x86480165, 0x0d060960, 0x00303130,
  };
  if (memcmp(enc_msg_ptr, kEncodedSha256, sizeof(kEncodedSha256)) != 0) {
    return kErrorSigverifyInvalidArgument;
  }
  enc_msg_ptr += ARRAYSIZE(kEncodedSha256);

  // Note: `kPsLen` excludes the last word of `enc_msg`, which is 0x0001ffff.
  static const size_t kPsLen = ARRAYSIZE(enc_msg->data) -
                               ARRAYSIZE(kEncodedSha256) -
                               ARRAYSIZE(act_digest->digest) - /*last word*/ 1;
  uint32_t padding = UINT32_MAX;
  for (size_t i = 0; i < kPsLen; ++i) {
    padding &= *enc_msg_ptr++;
  }
  uint32_t res = ~padding;
  res |= *enc_msg_ptr ^ 0x0001ffff;
  if (res != 0) {
    return kErrorSigverifyInvalidArgument;
  }

  return kErrorOk;
}

rom_error_t sigverify_rom_ext_signature_verify(
    const void *signed_region, size_t signed_region_len,
    const sigverify_rsa_buffer_t *signature, uint32_t key_id) {
  hmac_digest_t act_digest;
  hmac_sha256_init();
  RETURN_IF_ERROR(hmac_sha256_update(signed_region, signed_region_len));
  RETURN_IF_ERROR(hmac_sha256_final(&act_digest));

  // TODO(#21): Key validity check using OTP.
  const sigverify_rsa_key_t *key;
  RETURN_IF_ERROR(sigverify_rsa_key_get(key_id, &key));

  // TODO(#21): Choose between Ibex and OTBN using OTP.
  // TODO(#18): OTBN modular exponentiation.
  sigverify_rsa_buffer_t enc_msg;
  if (!sigverify_mod_exp_ibex(key, signature, &enc_msg)) {
    return kErrorSigverifyInvalidArgument;
  }
  RETURN_IF_ERROR(sigverify_padding_and_digest_check(&enc_msg, &act_digest));

  return kErrorOk;
}
