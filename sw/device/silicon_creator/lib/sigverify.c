// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/sigverify_mod_exp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

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
    return kErrorSigverifyBadEncodedMessage;
  }
  enc_msg_ptr += ARRAYSIZE(act_digest->digest);

  // Note: This also includes the zero byte right before PS.
  static const uint32_t kEncodedSha256[] = {
      0x05000420, 0x03040201, 0x86480165, 0x0d060960, 0x00303130,
  };
  if (memcmp(enc_msg_ptr, kEncodedSha256, sizeof(kEncodedSha256)) != 0) {
    return kErrorSigverifyBadEncodedMessage;
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
    return kErrorSigverifyBadEncodedMessage;
  }

  return kErrorOk;
}

/**
 * Determines whether the software implementation should be used for signature
 * verification.
 *
 * During manufacturing (TEST_UNLOCKED*), software implementation is used by
 * default since OTP may not have been programmed yet. The implementation to use
 * after manufacturing (PROD, PROD_END, DEV, RMA) is determined by the OTP
 * value.
 *
 * @param lc_state Life cycle state of the device.
 * @param[out] use_sw Use software implementation for signature verification.
 * @return Result of the operation.
 */
static rom_error_t sigverify_use_sw_rsa_verify(lifecycle_state_t lc_state,
                                               hardened_bool_t *use_sw) {
  switch (lc_state) {
    case kLcStateTestUnlocked0:
    case kLcStateTestUnlocked1:
    case kLcStateTestUnlocked2:
    case kLcStateTestUnlocked3:
    case kLcStateTestUnlocked4:
    case kLcStateTestUnlocked5:
    case kLcStateTestUnlocked6:
    case kLcStateTestUnlocked7:
      // Don't read from OTP during manufacturing. Use software
      // implementation by default.
      *use_sw = kHardenedBoolTrue;
      return kErrorOk;
    case kLcStateProd:
    case kLcStateProdEnd:
    case kLcStateDev:
    case kLcStateRma:
      *use_sw =
          otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET);
      return kErrorOk;
    default:
      return kErrorSigverifyBadLcState;
  }
}

rom_error_t sigverify_rsa_verify(const sigverify_rsa_buffer_t *signature,
                                 const sigverify_rsa_key_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state) {
  hardened_bool_t use_sw;
  RETURN_IF_ERROR(sigverify_use_sw_rsa_verify(lc_state, &use_sw));

  sigverify_rsa_buffer_t enc_msg;
  switch (use_sw) {
    case kHardenedBoolTrue:
      RETURN_IF_ERROR(sigverify_mod_exp_ibex(key, signature, &enc_msg));
      break;
    case kHardenedBoolFalse:
      RETURN_IF_ERROR(sigverify_mod_exp_otbn(key, signature, &enc_msg));
      break;
    default:
      return kErrorSigverifyBadOtpValue;
  }
  RETURN_IF_ERROR(sigverify_padding_and_digest_check(&enc_msg, act_digest));

  return kErrorOk;
}

void sigverify_usage_constraints_get(
    uint32_t selector_bits, manifest_usage_constraints_t *usage_constraints) {
  usage_constraints->selector_bits = selector_bits;
  lifecycle_device_id_get(&usage_constraints->device_id);
  // TODO(#7948): Define OTP entries for manufacturing states. Left unselected
  // for now.
  usage_constraints->manuf_state_creator =
      MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
  usage_constraints->manuf_state_owner =
      MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
  usage_constraints->life_cycle_state = lifecycle_state_get();

  static_assert(
      kManifestSelectorBitDeviceIdFirst == 0 &&
          kManifestSelectorBitDeviceIdLast == kLifecycleDeviceIdNumWords - 1,
      "mapping from selector_bits to device_id changed, loop must be updated");
  for (size_t i = 0; i < kLifecycleDeviceIdNumWords; ++i) {
    if (!bitfield_bit32_read(selector_bits, i)) {
      usage_constraints->device_id.device_id[i] =
          MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
    }
  }
  if (!bitfield_bit32_read(selector_bits,
                           kManifestSelectorBitManufStateCreator)) {
    usage_constraints->manuf_state_creator =
        MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
  }
  if (!bitfield_bit32_read(selector_bits,
                           kManifestSelectorBitManufStateOwner)) {
    usage_constraints->manuf_state_owner =
        MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
  }
  if (!bitfield_bit32_read(selector_bits, kManifestSelectorBitLifeCycleState)) {
    usage_constraints->life_cycle_state =
        MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
  }
}

// `extern` declarations for `inline` functions in the header.
extern uint32_t sigverify_rsa_key_id_get(const sigverify_rsa_buffer_t *modulus);
