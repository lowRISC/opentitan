// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sha2/sha384.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', '2', '3')

enum {
  /**
   * Maximum number of message chunks that the OTBN app can accept per run.
   *
   * This number is based on the DMEM size limit and usage by the masked SHA-384
   * app itself; see `run_sha384.s` for the detailed calculation.
   */
  kSha384MaxMessageChunksPerOtbnRun = 6,
};

/**
 * A type to hold message blocks.
 */
typedef struct sha384_message_block {
  uint32_t data[kSha384MessageBlockWords];
} sha384_message_block_t;

/**
 * Context object for the OTBN message buffer.
 */
typedef struct sha384_otbn_ctx {
  /**
   * Number of message blocks currently loaded.
   */
  size_t num_blocks;
} sha384_otbn_ctx_t;

// Initial state for SHA-384 (see FIPS 180-4, section 5.3.4).
// Stored in reverse dword order to match the 2-WDR layout of sha384_masked:
// Words 0..7  (WDR at offset 0, efgh): H[7], H[6], H[5], H[4] (low32, high32)
// Words 8..15 (WDR at offset 32, abcd): H[3], H[2], H[1], H[0] (low32, high32)
static const uint32_t kSha384InitialState[kSha384StateWords] = {
    0xbefa4fa4, 0x47b5481d, 0x64f98fa7, 0xdb0c2e0d, 0x68581511, 0x8eb44a87,
    0xffc00b31, 0x67332667, 0xf70e5939, 0x152fecd8, 0x3070dd17, 0x9159015a,
    0x367cd507, 0x629a292a, 0xc1059ed8, 0xcbbb9d5d,
};
static_assert(sizeof(kSha384InitialState) == kSha384StateBytes,
              "Initial state for SHA-384 has an unexpected size.");

OTBN_DECLARE_APP_SYMBOLS(run_sha384);            // The OTBN SHA-384 app.
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, state_s0);  // Hash state share 0.
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, state_s1);  // Hash state share 1.
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, msg_s0);    // Input message share 0.
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, msg_s1);    // Input message share 1.
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, n_chunks);  // Message length in blocks.

status_t sha384_init(sha384_state_t *state) {
  // Set the initial state.
  HARDENED_TRY(
      hardened_memcpy(state->H, kSha384InitialState, kSha384StateWords));
  // Set the partial block to 0 (the value is ignored).
  memset(state->partial_block, 0, sizeof(state->partial_block));
  // Set the message length so far to 0.
  state->total_len.lower = 0;
  state->total_len.upper = 0;

  return OTCRYPTO_OK;
}

/**
 * Calculate an updated total message length and check that it is acceptable.
 */
static status_t get_new_total_len(const sha384_state_t *state, size_t msg_len,
                                  sha384_message_length_t *new_total_len) {
  new_total_len->lower = state->total_len.lower + (msg_len << 3);
  new_total_len->upper = state->total_len.upper;
  if (new_total_len->lower < state->total_len.lower) {
    new_total_len->upper += 1;
  }
  if (new_total_len->upper < state->total_len.upper) {
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Run OTBN to process the data currently in DMEM.
 */
static status_t process_message_buffer(sha384_otbn_ctx_t *ctx) {
  const otbn_addr_t kOtbnVarSha384NChunks =
      OTBN_ADDR_T_INIT(run_sha384, n_chunks);
  HARDENED_TRY(otbn_dmem_write(1, &ctx->num_blocks, kOtbnVarSha384NChunks));

  HARDENED_TRY(otbn_execute());
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  ctx->num_blocks = 0;
  return OTCRYPTO_OK;
}

/**
 * Add a single message block to the processing buffer.
 *
 * Splits the block into two boolean shares using fresh Ibex randomness and
 * writes them to OTBN DMEM. Note that sha384_masked performs 64-bit
 * byte-swapping internally on OTBN.
 */
static status_t process_block(sha384_otbn_ctx_t *ctx,
                              const sha384_message_block_t *block) {
  size_t offset = ctx->num_blocks * kSha384MessageBlockBytes;
  const otbn_addr_t kOtbnVarSha384MsgS0 = OTBN_ADDR_T_INIT(run_sha384, msg_s0);
  const otbn_addr_t kOtbnVarSha384MsgS1 = OTBN_ADDR_T_INIT(run_sha384, msg_s1);

  uint32_t block_s0[kSha384MessageBlockWords];
  uint32_t block_s1[kSha384MessageBlockWords];
  for (size_t i = 0; i < kSha384MessageBlockWords; i++) {
    block_s1[i] = ibex_rnd32_read();
    block_s0[i] = block->data[i] ^ block_s1[i];
  }

  HARDENED_TRY(otbn_dmem_write(kSha384MessageBlockWords, block_s0,
                               kOtbnVarSha384MsgS0 + offset));
  HARDENED_TRY(otbn_dmem_write(kSha384MessageBlockWords, block_s1,
                               kOtbnVarSha384MsgS1 + offset));
  ctx->num_blocks += 1;

  if (ctx->num_blocks == kSha384MaxMessageChunksPerOtbnRun) {
    HARDENED_TRY(process_message_buffer(ctx));
  }
  return OTCRYPTO_OK;
}

/**
 * Pad the block as described in FIPS 180-4, section 5.1.2.
 */
static status_t process_padding(sha384_otbn_ctx_t *ctx,
                                const sha384_message_length_t total_len,
                                sha384_message_block_t *block) {
  size_t partial_block_len = (total_len.lower >> 3) % kSha384MessageBlockBytes;

  unsigned char *data_end = (unsigned char *)block->data + partial_block_len;
  size_t padding_len = kSha384MessageBlockBytes - partial_block_len;
  memset(data_end, 0, padding_len);
  memset(data_end, 0x80, 1);

  if (partial_block_len + 1 + 2 * sizeof(uint64_t) > kSha384MessageBlockBytes) {
    HARDENED_TRY(process_block(ctx, block));
    memset(block, 0, kSha384MessageBlockBytes);
  }

  block->data[kSha384MessageBlockWords - 1] =
      __builtin_bswap32(total_len.lower & UINT32_MAX);
  block->data[kSha384MessageBlockWords - 2] =
      __builtin_bswap32(total_len.lower >> 32);
  block->data[kSha384MessageBlockWords - 3] =
      __builtin_bswap32(total_len.upper & UINT32_MAX);
  block->data[kSha384MessageBlockWords - 4] =
      __builtin_bswap32(total_len.upper >> 32);

  return process_block(ctx, block);
}

/**
 * Update the hash state to include new data, optionally adding padding.
 */
static status_t process_message(sha384_state_t *state, const uint8_t *msg,
                                size_t msg_len,
                                hardened_bool_t padding_needed) {
  const otbn_app_t kOtbnAppSha384 = OTBN_APP_T_INIT(run_sha384);
  HARDENED_TRY(otbn_load_app(kOtbnAppSha384));

  sha384_state_t new_state;
  HARDENED_TRY(get_new_total_len(state, msg_len, &new_state.total_len));

  // Split the current hash state into two fresh boolean shares and write them
  // to OTBN DMEM (64 bytes per share, 2 contiguous WDRs).
  const otbn_addr_t kOtbnVarSha384StateS0 =
      OTBN_ADDR_T_INIT(run_sha384, state_s0);
  const otbn_addr_t kOtbnVarSha384StateS1 =
      OTBN_ADDR_T_INIT(run_sha384, state_s1);
  uint32_t state_s0[kSha384StateWords];
  uint32_t state_s1[kSha384StateWords];
  for (size_t i = 0; i < kSha384StateWords; i++) {
    state_s1[i] = ibex_rnd32_read();
    state_s0[i] = state->H[i] ^ state_s1[i];
  }
  HARDENED_TRY(
      otbn_dmem_write(kSha384StateWords, state_s0, kOtbnVarSha384StateS0));
  HARDENED_TRY(
      otbn_dmem_write(kSha384StateWords, state_s1, kOtbnVarSha384StateS1));

  sha384_message_block_t block;
  size_t partial_block_len =
      (state->total_len.lower >> 3) % kSha384MessageBlockBytes;
  HARDENED_TRY(hardened_memcpy(block.data, state->partial_block,
                               kSha384MessageBlockWords));

  sha384_otbn_ctx_t ctx = {.num_blocks = 0};

  while (msg_len >= kSha384MessageBlockBytes - partial_block_len) {
    size_t available_len = kSha384MessageBlockBytes - partial_block_len;
    memcpy((unsigned char *)block.data + partial_block_len, msg, available_len);
    msg += available_len;
    msg_len -= available_len;
    HARDENED_TRY(process_block(&ctx, &block));
    partial_block_len = 0;
  }

  memcpy((unsigned char *)block.data + partial_block_len, msg, msg_len);

  if (padding_needed == kHardenedBoolTrue) {
    HARDENED_TRY(process_padding(&ctx, new_state.total_len, &block));
  }

  if (ctx.num_blocks > 0) {
    HARDENED_TRY(process_message_buffer(&ctx));
  }

  // Read the final state shares from OTBN dmem and unmask.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kSha384StateWords, kOtbnVarSha384StateS0, state_s0));
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kSha384StateWords, kOtbnVarSha384StateS1, state_s1));
  for (size_t i = 0; i < kSha384StateWords; i++) {
    new_state.H[i] = state_s0[i] ^ state_s1[i];
  }

  HARDENED_TRY(otbn_dmem_sec_wipe());

  HARDENED_TRY(hardened_memcpy(state->H, new_state.H, kSha384StateWords));
  HARDENED_TRY(hardened_memcpy(state->partial_block, block.data,
                               kSha384MessageBlockWords));
  state->total_len.lower = new_state.total_len.lower;
  state->total_len.upper = new_state.total_len.upper;
  return OTCRYPTO_OK;
}

status_t sha384_update(sha384_state_t *state, const uint8_t *msg,
                       const size_t msg_len) {
  return process_message(state, msg, msg_len, kHardenedBoolFalse);
}

static status_t state_shred(sha384_state_t *state) {
  HARDENED_TRY(hardened_memshred(state->H, kSha384StateWords));
  HARDENED_TRY(
      hardened_memshred(state->partial_block, kSha384MessageBlockWords));
  state->total_len.lower = 0;
  state->total_len.upper = 0;

  return OTCRYPTO_OK;
}

/**
 * Copy the final SHA-384 digest as a byte-string.
 *
 * In our 16-word state layout, dword H[k] has its low 32 bits at H[14 - 2*k]
 * and its high 32 bits at H[15 - 2*k]. We output H[0]..H[5] (12 words = 48
 * bytes) in big-endian byte order per FIPS 180-4.
 */
static status_t sha384_digest_get(sha384_state_t *state, uint32_t *digest) {
  uint32_t out[kSha384DigestWords];
  for (size_t k = 0; k < kSha384DigestWords / 2; k++) {
    out[2 * k] = __builtin_bswap32(state->H[15 - 2 * k]);
    out[2 * k + 1] = __builtin_bswap32(state->H[14 - 2 * k]);
  }
  HARDENED_TRY(hardened_memcpy(digest, out, kSha384DigestWords));

  return OTCRYPTO_OK;
}

status_t sha384_final(sha384_state_t *state, uint32_t *digest) {
  HARDENED_TRY(process_message(state, NULL, 0, kHardenedBoolTrue));
  HARDENED_TRY(sha384_digest_get(state, digest));
  HARDENED_TRY(state_shred(state));
  return OTCRYPTO_OK;
}

status_t sha384(const uint8_t *msg, const size_t msg_len, uint32_t *digest) {
  sha384_state_t state;
  HARDENED_TRY(sha384_init(&state));
  HARDENED_TRY(process_message(&state, msg, msg_len, kHardenedBoolTrue));
  HARDENED_TRY(sha384_digest_get(&state, digest));
  HARDENED_TRY(state_shred(&state));
  return OTCRYPTO_OK;
}
