// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"

namespace rom_test {
extern "C" {
void hmac_sha256_init_endian(bool big_endian_digest) {
  MockHmac::Instance().sha256_init_endian(big_endian_digest);
}

void hmac_sha256_init(void) { MockHmac::Instance().sha256_init(); }

void hmac_sha256_update(const void *data, size_t len) {
  MockHmac::Instance().sha256_update(data, len);
}

void hmac_sha256_update_words(const uint32_t *data, size_t len) {
  MockHmac::Instance().sha256_update_words(data, len);
}

void hmac_sha256_final_truncated(uint32_t *digest, size_t len) {
  MockHmac::Instance().sha256_final_truncated(digest, len);
}

void hmac_sha256_final(hmac_digest_t *digest) {
  MockHmac::Instance().sha256_final(digest);
}

void hmac_sha256(const void *data, size_t len, hmac_digest_t *digest) {
  MockHmac::Instance().sha256(data, len, digest);
}
}  // extern "C"
}  // namespace rom_test
