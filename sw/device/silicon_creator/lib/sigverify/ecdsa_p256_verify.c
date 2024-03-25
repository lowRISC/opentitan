// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_verify.h"

#include "sw/device/silicon/creator/lib/otbn_boot_services.h"



rom_error_t sigverify_rsa_verify(const sigverify_ecdsa_p256_buffer_t *signature,
                                 const sigverify_ecdsa_p256_buffer_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state,
                                 uint32_t *flash_exec) {
  sigverify_rsa_buffer_t enc_msg;
  rom_error_t error = kErrorSigverifyEcdsaRsaSignature;

  // TODO(moidx): Initialize with random data.
  uint32_t result_r[kP256PublicKeyComponentWords];

  if (launder32(error) != kErrorOk) {
    *flash_exec ^= UINT32_MAX;
    return error;
  }
  HARDENED_CHECK_EQ(error, kErrorOk);
  return sigverify_encoded_message_check(&enc_msg, act_digest, flash_exec);
}

// Extern declarations for the inline functions in the header.
extern uint32_t sigverify_rsa_success_to_ok(uint32_t v);