// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"

namespace rom_test {
extern "C" {

hardened_bool_t ownership_key_validate(size_t page, ownership_key_t key,
                                       const owner_signature_t *signature,
                                       const void *message, size_t len) {
  return MockOwnershipKey::Instance().validate(page, key, signature, message,
                                               len);
}

rom_error_t ownership_seal_init() {
  return MockOwnershipKey::Instance().seal_init();
}

rom_error_t ownership_seal_page(size_t page) {
  return MockOwnershipKey::Instance().seal_page(page);
}

rom_error_t ownership_seal_check(size_t page) {
  return MockOwnershipKey::Instance().seal_check(page);
}

}  // extern "C"
}  // namespace rom_test
