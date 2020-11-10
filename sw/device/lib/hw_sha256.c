// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/hw_sha256.h"

#include "sw/device/lib/hmac.h"

static const HASH_VTAB HW_SHA256_VTAB = {.init = &hw_SHA256_init,
                                         .update = &hw_SHA256_update,
                                         .final = &hw_SHA256_final,
                                         .hash = &hw_SHA256_hash,
                                         .size = SHA256_DIGEST_SIZE};

static void sha256_init(void) {
  hmac_cfg_t config = {.mode = HMAC_OP_SHA256,
                       .input_endian_swap = 1,
                       .digest_endian_swap = 1,
                       .keys = {0}};
  hmac_init(config);
}

void hw_SHA256_init(HW_SHA256_CTX *ctx) {
  // TODO: For security, need to make sure HMAC is not stuck in progress.
  ctx->f = &HW_SHA256_VTAB;
  sha256_init();
}

void hw_SHA256_update(HW_SHA256_CTX *ctx, const void *data, size_t len) {
  hmac_update(data, len);
}

const uint8_t *hw_SHA256_final(HW_SHA256_CTX *ctx) {
  hmac_done((uint32_t *)ctx->buf);
  return ctx->buf;
}

const uint8_t *hw_SHA256_hash(const void *data, size_t len, uint8_t *digest) {
  sha256_init();
  hmac_update(data, len);
  hmac_done((uint32_t *)digest);
  return digest;
}
