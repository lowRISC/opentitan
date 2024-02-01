// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"

#include "sw/device/silicon_creator/lib/sigverify/spx_verify.h"
#include "sw/device/silicon_creator/rom/sigverify_keys.h"

#include "otp_ctrl_regs.h"

rom_error_t sigverify_spx_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_spx_key_t **key) {
  *key = NULL;
  uint32_t spx_en = sigverify_spx_verify_enabled(lc_state);
  rom_error_t error = kErrorSigverifyBadSpxKey;

  if (launder32(spx_en) != kSigverifySpxDisabledOtp) {
    const sigverify_rom_key_header_t *rom_key = NULL;
    error = sigverify_key_get(
        (sigverify_key_get_in_params_t){
            .key_id = key_id,
            .lc_state = lc_state,
            .key_array = (const sigverify_rom_key_header_t *)kSigverifySpxKeys,
            .otp_offset =
                OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN_OFFSET,
            .key_cnt = kSigverifySpxKeysCnt,
            .key_size = sizeof(sigverify_rom_spx_key_t),
            .step = kSigverifySpxKeysStep,
        },
        &rom_key);
    if (error == kErrorOk) {
      *key = &((const sigverify_rom_spx_key_t *)rom_key)->entry.key;
    }
  } else {
    HARDENED_CHECK_EQ(spx_en, kSigverifySpxDisabledOtp);
    error = sigverify_spx_success_to_ok(spx_en);
  }

  if (error != kErrorOk) {
    return kErrorSigverifyBadSpxKey;
  }
  return error;
}
