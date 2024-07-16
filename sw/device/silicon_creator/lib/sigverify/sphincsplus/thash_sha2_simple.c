// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/7ec789ace6874d875f4bb84cb61b81155398167e/ref/thash_sha2_simple.h

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/sha2.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"

void thash(const uint32_t *in, size_t inblocks, const spx_ctx_t *ctx,
           const spx_addr_t *addr, uint32_t *out) {
  hmac_sha256_restore(&ctx->state_seeded);
  hmac_sha256_update((unsigned char *)addr->addr, kSpxSha256AddrBytes);
  hmac_sha256_update_words(in, inblocks * kSpxNWords);
  hmac_sha256_process();
  hmac_sha256_final_truncated(out, kSpxNWords);
}
