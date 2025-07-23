// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"

namespace rom_test {
extern "C" {

rom_error_t ownership_key_validate(size_t page, ownership_key_t key,
                                   uint32_t command, const nonce_t *nonce,
                                   const owner_signature_t *signature,
                                   const void *message, size_t len,
                                   uint32_t *flash_exec) {
  return MockOwnershipKey::Instance().validate(
      page, key, command, nonce, signature, message, len, flash_exec);
}

rom_error_t ownership_seal_init(void) {
  return MockOwnershipKey::Instance().seal_init();
}

rom_error_t ownership_seal_page(size_t page) {
  return MockOwnershipKey::Instance().seal_page(page);
}

rom_error_t ownership_seal_check(size_t page) {
  return MockOwnershipKey::Instance().seal_check(page);
}

rom_error_t ownership_secret_new(uint32_t prior_key_alg,
                                 const owner_keydata_t *prior_owner_key) {
  return MockOwnershipKey::Instance().secret_new(prior_key_alg,
                                                 prior_owner_key);
}

}  // extern "C"
}  // namespace rom_test
