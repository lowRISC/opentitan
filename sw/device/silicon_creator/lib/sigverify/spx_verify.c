// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/spx_verify.h"

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "otp_ctrl_regs.h"

static uint32_t sigverify_spx_verify_enabled(lifecycle_state_t lc_state) {
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
      HARDENED_UNREACHABLE();
  }
}

rom_error_t sigverify_spx_verify(const sigverify_spx_signature_t *signature,
                                 const sigverify_spx_key_t *key,
                                 lifecycle_state_t lc_state,
                                 uint32_t *flash_exec) {
  uint32_t spx_en = launder32(sigverify_spx_verify_enabled(lc_state));
  rom_error_t error = kErrorSigverifyBadSpxSignature;
  if (launder32(spx_en) != kSigverifySpxDisabledOtp) {
    // FIXME: Implement this
  } else {
    HARDENED_CHECK_EQ(spx_en, kSigverifySpxDisabledOtp);
    *flash_exec ^= spx_en;
    uint32_t otp_val = sigverify_spx_verify_enabled(lc_state);
    // Note: `kSigverifySpxSuccess` is defined such that the following operation
    // produces `kErrorOk`.
    error = (((otp_val << 29) ^ ((otp_val << 29) >> 5) ^
              ((otp_val << 21) >> 10))) >>
            21;
  }
  if (error != kErrorOk) {
    return kErrorSigverifyBadSpxSignature;
  }
  return error;
}
