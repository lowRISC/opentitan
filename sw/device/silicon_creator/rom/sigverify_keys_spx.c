// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"

#include "sw/device/silicon_creator/lib/sigverify/spx_verify.h"
#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

#include "otp_ctrl_regs.h"

rom_error_t sigverify_spx_key_get(const sigverify_otp_key_ctx_t *sigverify_ctx,
                                  uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_spx_key_t **key,
                                  sigverify_spx_config_id_t *config) {
  *key = NULL;
  *config = 0;
  uint32_t spx_en = sigverify_spx_verify_enabled(lc_state);
  rom_error_t error = kErrorSigverifyBadSpxKey;

  if (launder32(spx_en) != kSigverifySpxDisabledOtp) {
    const sigverify_rom_key_header_t *rom_key = NULL;
    error = sigverify_otp_keys_get(
        (sigverify_otp_keys_get_params_t){
            .key_id = key_id,
            .lc_state = lc_state,
            .key_array =
                (const sigverify_rom_key_header_t *)(sigverify_ctx->keys.spx),
            .key_cnt = kSigVerifyOtpKeysSpxCount,
            .key_size = sizeof(sigverify_rom_spx_key_t),
            .key_states = (uint32_t *)&sigverify_ctx->states.spx[0],
        },
        &rom_key);
    if (error == kErrorOk) {
      *key = &((const sigverify_rom_spx_key_t *)rom_key)->entry.key;
      *config = ((const sigverify_rom_spx_key_t *)rom_key)->entry.config_id;
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
