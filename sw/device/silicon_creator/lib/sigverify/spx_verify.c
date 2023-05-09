// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/spx_verify.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"

#include "otp_ctrl_regs.h"

// Declared as a weak symbol so that we can override in tests. See
// spx_verify_functest.c.
OT_WEAK
uint32_t sigverify_spx_verify_enabled(lifecycle_state_t lc_state) {
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      // Don't read from OTP during manufacturing. Disable SPX+ signature
      // verification by default.
      return kSigverifySpxDisabledOtp;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      return otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_EN_OFFSET);
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      return otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_EN_OFFSET);
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      return otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_EN_OFFSET);
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_EN_OFFSET);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

/**
 * Shares for producing the `flash_exec_spx` value in `sigverify_spx_verify()`
 * when SPHINCS+ signature verification is enabled. First 3 shares are generated
 * using the `sparse-fsm-encode` script while the last share is
 * `kSigverifySpxSuccess ^ kSpxShares[0] ^ ... ^ kSpxShares[2]` so that xor'ing
 * all shares produces `kSigverifySpxSuccess`.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 3 -n 32 \
 *     -s 327911352 --language=c
 *
 * Minimum Hamming distance: 15
 * Maximum Hamming distance: 19
 * Minimum Hamming weight: 10
 * Maximum Hamming weight: 17
 */
static const uint32_t kSpxVerifyShares[kSigverifySpxRootNumWords] = {
    0xa5bda1e8,
    0x229044e4,
    0x94eadad8,
    0x9eabb3c3,
};

rom_error_t sigverify_spx_verify(
    const sigverify_spx_signature_t *signature, const sigverify_spx_key_t *key,
    lifecycle_state_t lc_state, const void *msg_prefix_1,
    size_t msg_prefix_1_len, const void *msg_prefix_2, size_t msg_prefix_2_len,
    const void *msg, size_t msg_len, uint32_t *flash_exec) {
  uint32_t spx_en = launder32(sigverify_spx_verify_enabled(lc_state));
  rom_error_t error = kErrorSigverifyBadSpxSignature;
  if (launder32(spx_en) != kSigverifySpxDisabledOtp) {
    sigverify_spx_root_t expected_root;
    spx_public_key_root(key->data, expected_root.data);
    sigverify_spx_root_t actual_root;
    HARDENED_RETURN_IF_ERROR(spx_verify(
        signature->data, msg_prefix_1, msg_prefix_1_len, msg_prefix_2,
        msg_prefix_2_len, msg, msg_len, key->data, actual_root.data));

    size_t i = 0;
    for (; launder32(i) < kSigverifySpxRootNumWords; ++i) {
      actual_root.data[i] ^= expected_root.data[i] ^ kSpxVerifyShares[i];
    }
    HARDENED_CHECK_EQ(i, kSigverifySpxRootNumWords);
    uint32_t flash_exec_spx = 0;
    uint32_t diff = 0;
    for (--i; launder32(i) < kSigverifySpxRootNumWords; --i) {
      // Following three statements set `diff` to `UINT32_MAX` if
      // `actual_root[i]` is incorrect, no change otherwise.
      diff |= actual_root.data[i] ^ kSpxVerifyShares[i];
      diff |= ~diff + 1;  // Set upper bits to 1 if not 0, no change o/w.
      diff |= ~(diff >> 31) + 1;  // Set to all 1s if MSB is set, no change o/w.

      flash_exec_spx ^= actual_root.data[i];
      // Set `flash_exec_spx` to `UINT32_MAX` if `actual_root` is incorrect.
      flash_exec_spx |= diff;
    }
    HARDENED_CHECK_EQ(i, UINT32_MAX);
    error = sigverify_spx_success_to_ok(flash_exec_spx);
    *flash_exec ^= flash_exec_spx;
  } else {
    HARDENED_CHECK_EQ(spx_en, kSigverifySpxDisabledOtp);
    *flash_exec ^= spx_en;
    uint32_t otp_val = sigverify_spx_verify_enabled(lc_state);
    // Note: `kSigverifySpxSuccess` is defined such that the following operation
    // produces `kErrorOk`.
    error = sigverify_spx_success_to_ok(otp_val);
  }
  if (error != kErrorOk) {
    return kErrorSigverifyBadSpxSignature;
  }
  return error;
}

// Extern declarations for the inline functions in the header.
extern uint32_t sigverify_spx_success_to_ok(uint32_t v);
