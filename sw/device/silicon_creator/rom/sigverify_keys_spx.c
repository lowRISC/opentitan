// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"

#include "sw/device/silicon_creator/rom/sigverify_keys.h"

#include "otp_ctrl_regs.h"

rom_error_t sigverify_spx_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_spx_key_t **key) {
  const sigverify_rom_key_header_t *rom_key = NULL;
  rom_error_t error = sigverify_key_get(
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
  if (error != kErrorOk) {
    return kErrorSigverifyBadSpxKey;
  }
  *key = &((const sigverify_rom_spx_key_t *)rom_key)->entry.key;
  return error;
}
