// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"

namespace rom_test {
extern "C" {
void hmac_sha256_configure(bool big_endian_digest) {
  MockHmac::Instance().sha256_configure(big_endian_digest);
}

void hmac_sha256_start(void) { MockHmac::Instance().sha256_start(); }

void hmac_sha256_init(void) { MockHmac::Instance().sha256_init(); }

void hmac_sha256_update(const void *data, size_t len) {
  MockHmac::Instance().sha256_update(data, len);
}

void hmac_sha256_update_words(const uint32_t *data, size_t len) {
  MockHmac::Instance().sha256_update_words(data, len);
}

void hmac_sha256_process(void) { MockHmac::Instance().sha256_process(); }

void hmac_sha256_final_truncated(uint32_t *digest, size_t len) {
  MockHmac::Instance().sha256_final_truncated(digest, len);
}

void hmac_sha256_final(hmac_digest_t *digest) {
  MockHmac::Instance().sha256_final(digest);
}

void hmac_sha256(const void *data, size_t len, hmac_digest_t *digest) {
  MockHmac::Instance().sha256(data, len, digest);
}

void hmac_sha256_save(hmac_context_t *ctx) {
  MockHmac::Instance().sha256_save(ctx);
}

void hmac_sha256_restore(const hmac_context_t *ctx) {
  MockHmac::Instance().sha256_restore(ctx);
}
}  // extern "C"
}  // namespace rom_test
