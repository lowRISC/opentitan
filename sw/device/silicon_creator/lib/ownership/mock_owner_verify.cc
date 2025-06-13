// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/mock_owner_verify.h"

namespace rom_test {
extern "C" {

rom_error_t owner_verify(uint32_t key_alg, const owner_keydata_t *key,
                         const ecdsa_p256_signature_t *ecdsa_sig,
                         const sigverify_spx_signature_t *spx_sig,
                         const void *msg_prefix_1, size_t msg_prefix_1_len,
                         const void *msg_prefix_2, size_t msg_prefix_2_len,
                         const void *msg, size_t msg_len,
                         const hmac_digest_t *digest, uint32_t *flash_exec) {
  return MockOwnerVerify::Instance().verify(
      key_alg, key, ecdsa_sig, spx_sig, msg_prefix_1, msg_prefix_1_len,
      msg_prefix_2, msg_prefix_2_len, msg, msg_len, digest, flash_exec);
}

}  // extern "C"
}  // namespace rom_test
