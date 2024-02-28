// Copyright lowRISC contributors.
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

}  // extern "C"
}  // namespace rom_test
