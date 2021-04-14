// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for hmac.c.
 */
class MockHmac {
 public:
  MOCK_METHOD(rom_error_t, sha256_init, (const hmac_t *));
  MOCK_METHOD(rom_error_t, sha256_update,
              (const hmac_t *, const void *, size_t));
  MOCK_METHOD(rom_error_t, sha256_final, (const hmac_t *, hmac_digest_t *));
  virtual ~MockHmac() {}
};

}  // namespace internal

using MockHmac = GlobalMock<testing::StrictMock<internal::MockHmac>>;

extern "C" {

rom_error_t hmac_sha256_init(const hmac_t *hmac) {
  return MockHmac::Instance().sha256_init(hmac);
}

rom_error_t hmac_sha256_update(const hmac_t *hmac, const void *data,
                               size_t len) {
  return MockHmac::Instance().sha256_update(hmac, data, len);
}

rom_error_t hmac_sha256_final(const hmac_t *hmac, hmac_digest_t *digest) {
  return MockHmac::Instance().sha256_final(hmac, digest);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_
