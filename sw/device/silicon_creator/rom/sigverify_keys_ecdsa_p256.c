// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys_ecdsa_p256.h"

#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

#include "otp_ctrl_regs.h"

rom_error_t sigverify_ecdsa_p256_key_get(
    const sigverify_otp_key_ctx_t *sigverify_ctx, uint32_t key_id,
    lifecycle_state_t lc_state, const sigverify_ecdsa_p256_buffer_t **key) {
  *key = NULL;
  rom_error_t error = kErrorSigverifyBadEcdsaKey;

  const sigverify_rom_key_header_t *rom_key = NULL;
  error = sigverify_otp_keys_get(
      (sigverify_otp_keys_get_params_t){
          .key_id = key_id,
          .lc_state = lc_state,
          .key_array =
              (const sigverify_rom_key_header_t *)(sigverify_ctx->keys.ecdsa),
          .key_cnt = kSigVerifyOtpKeysEcdsaCount,
          .key_size = sizeof(sigverify_rom_ecdsa_p256_key_t),
          .key_states = (uint32_t *)&sigverify_ctx->states.ecdsa[0],
      },
      &rom_key);
  if (error == kErrorOk) {
    *key = &((const sigverify_rom_ecdsa_p256_key_t *)rom_key)->entry.key;
  }

  if (error != kErrorOk) {
    return kErrorSigverifyBadEcdsaKey;
  }
  return error;
}
