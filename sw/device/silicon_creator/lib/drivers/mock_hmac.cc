// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"

namespace rom_test {
extern "C" {
void hmac_sha256_init(void) { MockHmac::Instance().sha256_init(); }

void hmac_sha256_update(const void *data, size_t len) {
  MockHmac::Instance().sha256_update(data, len);
}

void hmac_sha256_final(hmac_digest_t *digest) {
  MockHmac::Instance().sha256_final(digest);
}

void hmac_sha256(const void *data, size_t len, hmac_digest_t *digest) {
  MockHmac::Instance().sha256(data, len, digest);
}
}  // extern "C"
}  // namespace rom_test
