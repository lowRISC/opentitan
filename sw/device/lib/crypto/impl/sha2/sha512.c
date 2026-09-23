// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sha2/sha512.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', '2', '5')

enum {
  /**
   * Maximum number of message chunks that the OTBN app can accept per run.
   *
   * This number is based on the DMEM size limit and usage by the masked SHA-512
   * app itself; see `run_sha512.s` for the detailed calculation.
   */
  kSha512MaxMessageChunksPerOtbnRun = 6,
};

/**
 * A type to hold message blocks.
 */
typedef struct sha512_message_block {
  uint32_t data[kSha512MessageBlockWords];
} sha512_message_block_t;

/**
 * Context object for the OTBN message buffer.
 */
typedef struct sha512_otbn_ctx {
  /**
   * Number of message blocks currently loaded.
   */
  size_t num_blocks;
} sha512_otbn_ctx_t;

// Initial state for SHA-512 (see FIPS 180-4, section 5.3.5).
// Stored in reverse dword order to match the 2-WDR layout of sha512_masked:
// Words 0..7  (WDR at offset 0, efgh): H[7], H[6], H[5], H[4] (low32, high32)
// Words 8..15 (WDR at offset 32, abcd): H[3], H[2], H[1], H[0] (low32, high32)
static const uint32_t kSha512InitialState[kSha512StateWords] = {
    0x137e2179, 0x5be0cd19, 0xfb41bd6b, 0x1f83d9ab, 0x2b3e6c1f, 0x9b05688c,
    0xade682d1, 0x510e527f, 0x5f1d36f1, 0xa54ff53a, 0xfe94f82b, 0x3c6ef372,
    0x84caa73b, 0xbb67ae85, 0xf3bcc908, 0x6a09e667,
};
static_assert(sizeof(kSha512InitialState) == kSha512StateBytes,
              "Initial state for SHA-512 has an unexpected size.");

OTBN_DECLARE_APP_SYMBOLS(run_sha512);            // The OTBN SHA-512 app.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, state_s0);  // Hash state share 0.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, state_s1);  // Hash state share 1.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, msg_s0);    // Input message share 0.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, msg_s1);    // Input message share 1.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, n_chunks);  // Message length in blocks.

status_t sha512_init(sha512_state_t *state) {
  // Set the initial state.
  HARDENED_TRY(
      hardened_memcpy(state->H, kSha512InitialState, kSha512StateWords));
  // Set the partial block to 0 (the value is ignored).
  memset(state->partial_block, 0, sizeof(state->partial_block));
  // Set the message length so far to 0.
  state->total_len.lower = 0;
  state->total_len.upper = 0;

  return OTCRYPTO_OK;
}

/**
 * Calculate an updated total message length and check that it is acceptable.
 *
 * Returns `OTCRYPTO_BAD_ARGS` if the current message length plus the new
 * message length exceeds the SHA-512 maximum of 2^128 bits.
 *
 * @param state Context object.
 * @param msg_len Length of new data in bytes.
 * @param[out] new_total_len New total received data length.
 * @return Result of the operation.
 */
static status_t get_new_total_len(const sha512_state_t *state, size_t msg_len,
                                  sha512_message_length_t *new_total_len) {
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
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @return Result of the operation.
 */
static status_t process_message_buffer(sha512_otbn_ctx_t *ctx) {
  const otbn_addr_t kOtbnVarSha512NChunks =
      OTBN_ADDR_T_INIT(run_sha512, n_chunks);
  HARDENED_TRY(otbn_dmem_write(1, &ctx->num_blocks, kOtbnVarSha512NChunks));

  HARDENED_TRY(otbn_execute());
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  ctx->num_blocks = 0;
  return OTCRYPTO_OK;
}

/**
 * Add a single message block to the processing buffer.
 *
 * Splits the block into two boolean shares using fresh Ibex randomness and
 * writes them to OTBN DMEM. Note that sha512_masked performs 64-bit
 * byte-swapping internally on OTBN.
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @param block Block to write.
 * @return Result of the operation.
 */
static status_t process_block(sha512_otbn_ctx_t *ctx,
                              const sha512_message_block_t *block) {
  size_t offset = ctx->num_blocks * kSha512MessageBlockBytes;
  const otbn_addr_t kOtbnVarSha512MsgS0 = OTBN_ADDR_T_INIT(run_sha512, msg_s0);
  const otbn_addr_t kOtbnVarSha512MsgS1 = OTBN_ADDR_T_INIT(run_sha512, msg_s1);

  uint32_t block_s0[kSha512MessageBlockWords];
  uint32_t block_s1[kSha512MessageBlockWords];
  for (size_t i = 0; i < kSha512MessageBlockWords; i++) {
    block_s1[i] = ibex_rnd32_read();
    block_s0[i] = block->data[i] ^ block_s1[i];
  }

  HARDENED_TRY(otbn_dmem_write(kSha512MessageBlockWords, block_s0,
                               kOtbnVarSha512MsgS0 + offset));
  HARDENED_TRY(otbn_dmem_write(kSha512MessageBlockWords, block_s1,
                               kOtbnVarSha512MsgS1 + offset));
  ctx->num_blocks += 1;

  if (ctx->num_blocks == kSha512MaxMessageChunksPerOtbnRun) {
    HARDENED_TRY(process_message_buffer(ctx));
  }
  return OTCRYPTO_OK;
}

/**
 * Pad the block as described in FIPS 180-4, section 5.1.2.
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @param total_len Total length of message so far.
 * @param block Current (partial) block.
 * @return Result of the operation.
 */
static status_t process_padding(sha512_otbn_ctx_t *ctx,
                                const sha512_message_length_t total_len,
                                sha512_message_block_t *block) {
  size_t partial_block_len = (total_len.lower >> 3) % kSha512MessageBlockBytes;

  unsigned char *data_end = (unsigned char *)block->data + partial_block_len;
  size_t padding_len = kSha512MessageBlockBytes - partial_block_len;
  memset(data_end, 0, padding_len);
  memset(data_end, 0x80, 1);

  if (partial_block_len + 1 + 2 * sizeof(uint64_t) > kSha512MessageBlockBytes) {
    HARDENED_TRY(process_block(ctx, block));
    memset(block, 0, kSha512MessageBlockBytes);
  }

  block->data[kSha512MessageBlockWords - 1] =
      __builtin_bswap32(total_len.lower & UINT32_MAX);
  block->data[kSha512MessageBlockWords - 2] =
      __builtin_bswap32(total_len.lower >> 32);
  block->data[kSha512MessageBlockWords - 3] =
      __builtin_bswap32(total_len.upper & UINT32_MAX);
  block->data[kSha512MessageBlockWords - 4] =
      __builtin_bswap32(total_len.upper >> 32);

  return process_block(ctx, block);
}

/**
 * Update the hash state to include new data, optionally adding padding.
 *
 * @param state Context object.
 * @param msg Input message.
 * @param msg_len Input message length in bytes.
 * @param padding_needed Whether to pad the message.
 * @return Result of the operation.
 */
static status_t process_message(sha512_state_t *state, const uint8_t *msg,
                                size_t msg_len,
                                hardened_bool_t padding_needed) {
  const otbn_app_t kOtbnAppSha512 = OTBN_APP_T_INIT(run_sha512);
  HARDENED_TRY(otbn_load_app(kOtbnAppSha512));

  sha512_state_t new_state;
  HARDENED_TRY(get_new_total_len(state, msg_len, &new_state.total_len));

  // Split the current hash state into two fresh boolean shares and write them
  // to OTBN DMEM (64 bytes per share, 2 contiguous WDRs).
  const otbn_addr_t kOtbnVarSha512StateS0 =
      OTBN_ADDR_T_INIT(run_sha512, state_s0);
  const otbn_addr_t kOtbnVarSha512StateS1 =
      OTBN_ADDR_T_INIT(run_sha512, state_s1);
  uint32_t state_s0[kSha512StateWords];
  uint32_t state_s1[kSha512StateWords];
  for (size_t i = 0; i < kSha512StateWords; i++) {
    state_s1[i] = ibex_rnd32_read();
    state_s0[i] = state->H[i] ^ state_s1[i];
  }
  HARDENED_TRY(
      otbn_dmem_write(kSha512StateWords, state_s0, kOtbnVarSha512StateS0));
  HARDENED_TRY(
      otbn_dmem_write(kSha512StateWords, state_s1, kOtbnVarSha512StateS1));

  sha512_message_block_t block;
  size_t partial_block_len =
      (state->total_len.lower >> 3) % kSha512MessageBlockBytes;
  HARDENED_TRY(hardened_memcpy(block.data, state->partial_block,
                               kSha512MessageBlockWords));

  sha512_otbn_ctx_t ctx = {.num_blocks = 0};

  while (msg_len >= kSha512MessageBlockBytes - partial_block_len) {
    size_t available_len = kSha512MessageBlockBytes - partial_block_len;
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
      otbn_dmem_read(kSha512StateWords, kOtbnVarSha512StateS0, state_s0));
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kSha512StateWords, kOtbnVarSha512StateS1, state_s1));
  for (size_t i = 0; i < kSha512StateWords; i++) {
    new_state.H[i] = state_s0[i] ^ state_s1[i];
  }

  HARDENED_TRY(otbn_dmem_sec_wipe());

  HARDENED_TRY(hardened_memcpy(state->H, new_state.H, kSha512StateWords));
  HARDENED_TRY(hardened_memcpy(state->partial_block, block.data,
                               kSha512MessageBlockWords));
  state->total_len.lower = new_state.total_len.lower;
  state->total_len.upper = new_state.total_len.upper;
  return OTCRYPTO_OK;
}

status_t sha512_update(sha512_state_t *state, const uint8_t *msg,
                       const size_t msg_len) {
  return process_message(state, msg, msg_len, kHardenedBoolFalse);
}

static status_t state_shred(sha512_state_t *state) {
  HARDENED_TRY(hardened_memshred(state->H, kSha512StateWords));
  HARDENED_TRY(
      hardened_memshred(state->partial_block, kSha512MessageBlockWords));
  state->total_len.lower = 0;
  state->total_len.upper = 0;

  return OTCRYPTO_OK;
}

/**
 * Copy the final SHA-512 digest as a byte-string.
 *
 * In our 16-word state layout, dword H[k] has its low 32 bits at H[14 - 2*k]
 * and its high 32 bits at H[15 - 2*k]. We output H[0]..H[7] (16 words = 64
 * bytes) in big-endian byte order per FIPS 180-4.
 *
 * @param state Context object.
 * @param[out] digest Destination buffer for digest.
 * @return OK or error.
 */
static status_t sha512_digest_get(sha512_state_t *state, uint32_t *digest) {
  uint32_t out[kSha512DigestWords];
  for (size_t k = 0; k < kSha512DigestWords / 2; k++) {
    out[2 * k] = __builtin_bswap32(state->H[15 - 2 * k]);
    out[2 * k + 1] = __builtin_bswap32(state->H[14 - 2 * k]);
  }
  HARDENED_TRY(hardened_memcpy(digest, out, kSha512DigestWords));

  return OTCRYPTO_OK;
}

status_t sha512_final(sha512_state_t *state, uint32_t *digest) {
  HARDENED_TRY(process_message(state, NULL, 0, kHardenedBoolTrue));
  HARDENED_TRY(sha512_digest_get(state, digest));
  HARDENED_TRY(state_shred(state));
  return OTCRYPTO_OK;
}

status_t sha512(const uint8_t *msg, const size_t msg_len, uint32_t *digest) {
  sha512_state_t state;
  HARDENED_TRY(sha512_init(&state));
  HARDENED_TRY(process_message(&state, msg, msg_len, kHardenedBoolTrue));
  HARDENED_TRY(sha512_digest_get(&state, digest));
  HARDENED_TRY(state_shred(&state));
  return OTCRYPTO_OK;
}
