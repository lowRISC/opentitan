// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sha2/sha256.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', '2', '2')

enum {
  /**
   * Maximum number of message chunks that the OTBN app can accept.
   *
   * This number is based on the DMEM size limit and usage by the SHA-256 app
   * itself; see `run_sha256.s` for the detailed calculation.
   */
  kSha256MaxMessageChunksPerOtbnRun = 41,
};

/**
 * A type to hold message blocks.
 */
typedef struct sha256_message_block {
  uint32_t data[kSha256MessageBlockWords];
} sha256_message_block_t;

/**
 * Context object for the OTBN message buffer.
 */
typedef struct sha256_otbn_ctx {
  /**
   * Number of message blocks currently loaded.
   */
  size_t num_blocks;
} sha256_otbn_ctx_t;

// Initial state for SHA-256 (see FIPS 180-4, section 5.3.3). The SHA-256 OTBN
// app represents the state with little-endian words and in reverse word-order
// compared with FIPS 180-4.
static const uint32_t kSha256InitialState[kSha256StateWords] = {
    0x5be0cd19, 0x1f83d9ab, 0x9b05688c, 0x510e527f,
    0xa54ff53a, 0x3c6ef372, 0xbb67ae85, 0x6a09e667,
};
static_assert(sizeof(kSha256InitialState) == kSha256StateBytes,
              "Initial state for SHA-256 has an unexpected size.");

OTBN_DECLARE_APP_SYMBOLS(run_sha256);         // The OTBN SHA-256 app.
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, state);  // Hash state.
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, msg);    // Input message.
OTBN_DECLARE_SYMBOL_ADDR(run_sha256,
                         num_msg_chunks);  // Message length in blocks.

static const otbn_app_t kOtbnAppSha256 = OTBN_APP_T_INIT(run_sha256);
static const otbn_addr_t kOtbnVarSha256State =
    OTBN_ADDR_T_INIT(run_sha256, state);
static const otbn_addr_t kOtbnVarSha256Msg = OTBN_ADDR_T_INIT(run_sha256, msg);
static const otbn_addr_t kOtbnVarSha256NumMsgChunks =
    OTBN_ADDR_T_INIT(run_sha256, num_msg_chunks);

void sha256_init(sha256_state_t *state) {
  // Set the initial state.
  hardened_memcpy(state->H, kSha256InitialState, kSha256StateWords);
  // Set the partial block to 0 (the value is ignored).
  memset(state->partial_block, 0, kSha256MessageBlockBytes);
  // Set the message length so far to 0.
  state->total_len = 0ull;
}

/**
 * Pad the block as described in FIPS 180-4, section 5.1.2.
 *
 * Padding fills the current block and may require one additional block.
 *
 * The length of real data in the partial block should be the byte-length of
 * the message so far (total_len >> 3) modulo `kSha256MessageBlockBytes`.
 *
 * @param total_len Total length of message so far.
 * @param block Current (partial) block, updated in-place.
 * @param[out] additional_block Buffer for an additional padding block.
 * @return Length of padding added in bytes.
 * @return Result of the operation.
 */
static size_t add_padding(const uint64_t total_len,
                          sha256_message_block_t *block,
                          sha256_message_block_t *additional_block) {
  size_t partial_block_len = (total_len >> 3) % kSha256MessageBlockBytes;

  // Get a byte-sized pointer to the end of the real data within the block.
  unsigned char *data_end = (unsigned char *)block->data + partial_block_len;

  // Fill the remainder of the block with zeroes.
  size_t padding_len = kSha256MessageBlockBytes - partial_block_len;
  memset(data_end, 0, padding_len);

  // Set the last byte after the message to 0x80. There must be at least one
  // unfilled byte in the partial block, since partial_block_len is always <
  // kSha256MessageBlockBytes.
  memset(data_end, 0x80, 1);

  sha256_message_block_t *final_block = block;
  if (partial_block_len + 1 + sizeof(total_len) > kSha256MessageBlockBytes) {
    // We need the additional block; partial data + 0x80 + 8-byte encoding of
    // length will not fit in the current block.
    memset(additional_block, 0, kSha256MessageBlockBytes);
    padding_len += kSha256MessageBlockBytes;
    final_block = additional_block;
  }

  // Set the last 64 bits of the final block to the bit-length in big-endian
  // form.
  final_block->data[kSha256MessageBlockWords - 1] =
      __builtin_bswap32(total_len & UINT32_MAX);
  final_block->data[kSha256MessageBlockWords - 2] =
      __builtin_bswap32(total_len >> 32);
  return padding_len;
}

/**
 * Run OTBN to process the data currently in DMEM.
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @return Result of the operation.
 */
static status_t process_message_buffer(sha256_otbn_ctx_t *ctx) {
  // Write the number of blocks to DMEM.
  HARDENED_TRY(
      otbn_dmem_write(1, &ctx->num_blocks, kOtbnVarSha256NumMsgChunks));

  // Run the OTBN program.
  HARDENED_TRY(otbn_execute());
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Reset the message buffer counter.
  ctx->num_blocks = 0;
  return OTCRYPTO_OK;
}

/**
 * Add a single message block to the processing buffer.
 *
 * Runs OTBN if the maximum number of message blocks has been reached.
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @param block Block to write.
 * @return Result of the operation.
 */
static status_t process_block(sha256_otbn_ctx_t *ctx,
                              const sha256_message_block_t *block) {
  // Calculate the offset within the message buffer.
  size_t offset = ctx->num_blocks * kSha256MessageBlockBytes;
  otbn_addr_t dst = kOtbnVarSha256Msg + offset;

  // Copy the message block into DMEM.
  otbn_dmem_write(kSha256MessageBlockWords, block->data, dst);
  ctx->num_blocks += 1;

  // If we've reached the maximum number of message chunks for a single run,
  // then run the OTBN program to update the state in-place. Note that there
  // is no need to read back and then re-write the state; it'll stay updated
  // in DMEM for the next run.
  if (ctx->num_blocks == kSha256MaxMessageChunksPerOtbnRun) {
    HARDENED_TRY(process_message_buffer(ctx));
  }
  return OTCRYPTO_OK;
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
static status_t process_message(sha256_state_t *state, const uint8_t *msg,
                                size_t msg_len,
                                hardened_bool_t padding_needed) {
  // Load the SHA-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppSha256));

  // Check the message length. SHA-256 messages must be less than 2^64 bits
  // long in total.
  uint64_t msg_bits = ((uint64_t)msg_len) << 3;
  uint64_t max_msg_bits = UINT64_MAX - state->total_len;
  if (msg_bits > max_msg_bits) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Calculate the new value of state->total_len. Do NOT update the state yet
  // (because if we get an OTBN error, it would become out of sync).
  sha256_state_t new_state;
  new_state.total_len = state->total_len + msg_bits;

  // Set the initial state if at least one block has been received before now.
  if (state->total_len >= kSha256MessageBlockBytes) {
    HARDENED_TRY(
        otbn_dmem_write(kSha256StateWords, state->H, kOtbnVarSha256State));
  }

  // Start computing the first block for the hash computation by simply copying
  // the partial block. We won't use the partial block directly to avoid
  // contaminating the context object if this operation fails later.
  sha256_message_block_t block;
  size_t partial_block_len = (state->total_len >> 3) % kSha256MessageBlockBytes;
  memcpy(block.data, state->partial_block, partial_block_len);

  // Initialize the context for the OTBN message buffer.
  sha256_otbn_ctx_t ctx = {.num_blocks = 0};

  // Process the message one block at a time, including partial data if it is
  // present (which is only possible on the first iteration).
  while (msg_len >= kSha256MessageBlockBytes - partial_block_len) {
    size_t available_len = kSha256MessageBlockBytes - partial_block_len;
    memcpy((unsigned char *)block.data + partial_block_len, msg, available_len);
    msg += available_len;
    msg_len -= available_len;
    HARDENED_TRY(process_block(&ctx, &block));
    partial_block_len = 0;
  }

  // Copy remaining mesage data into the working block (after partial data, if
  // it is present). Because of the loop condition above, this must not be a
  // full block.
  memcpy((unsigned char *)block.data + partial_block_len, msg, msg_len);

  // Add padding if necessary.
  if (padding_needed == kHardenedBoolTrue) {
    sha256_message_block_t additional_block;
    size_t padding_len =
        add_padding(new_state.total_len, &block, &additional_block);
    // We always fill `block`; process it.
    HARDENED_TRY(process_block(&ctx, &block));
    // Check if `additional_block` was used, and process it if so.
    if (padding_len > kSha256MessageBlockBytes) {
      HARDENED_TRY(process_block(&ctx, &additional_block));
    }
  }

  // If there are any unprocessed blocks currently in DMEM, run the program one
  // final time.
  if (ctx.num_blocks > 0) {
    HARDENED_TRY(process_message_buffer(&ctx));
  }

  // Read the final state from OTBN dmem.
  HARDENED_TRY(
      otbn_dmem_read(kSha256StateWords, kOtbnVarSha256State, new_state.H));

  // Clear OTBN's memory.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  // At this point, no more errors are possible; it is safe to update the
  // context object.
  hardened_memcpy(state->H, new_state.H, kSha256StateWords);
  hardened_memcpy(state->partial_block, block.data, kSha256MessageBlockWords);
  state->total_len = new_state.total_len;
  return OTCRYPTO_OK;
}

status_t sha256_update(sha256_state_t *state, const uint8_t *msg,
                       const size_t msg_len) {
  // Process new data with no padding.
  return process_message(state, msg, msg_len, kHardenedBoolFalse);
}

/**
 * Replace sensitive data in a SHA-256 context with non-sensitive values.
 *
 * @param state The context object to shred.
 */
static void state_shred(sha256_state_t *state) {
  hardened_memshred(state->H, kSha256StateWords);
  hardened_memshred(state->partial_block, kSha256MessageBlockWords);
  state->total_len = 0;
}

/**
 * Copy the final digest as a byte-string.
 *
 * SHA-256 intermediate computations use words in little-endian format, but the
 * FIPS 180-4 spec requires big-endian words (see section 3.1). Therefore, to
 * get the right final byte-order, we need to reverse each word in the state.
 *
 * Also, in the SHA-256 computation, the order of the words is reversed
 * compared to FIPS 180-4, so we switch the word order as well.
 *
 * @param state Context object.
 * @param[out] digest Destination buffer for digest.
 */
static void digest_get(sha256_state_t *state, uint8_t *digest) {
  for (size_t i = 0; i < kSha256StateWords / 2; i++) {
    uint32_t tmp = __builtin_bswap32(state->H[i]);
    state->H[i] = __builtin_bswap32(state->H[kSha256StateWords - 1 - i]);
    state->H[kSha256StateWords - 1 - i] = tmp;
  }
  // TODO(#17711): this can be `hardened_memcpy` if `digest` is aligned.
  memcpy(digest, state->H, kSha256StateBytes);
}

status_t sha256_final(sha256_state_t *state, uint8_t *digest) {
  // Construct padding.
  HARDENED_TRY(process_message(state, NULL, 0, kHardenedBoolTrue));

  // Retrieve the final digest and destroy the state.
  digest_get(state, digest);
  state_shred(state);
  return OTCRYPTO_OK;
}

status_t sha256(const uint8_t *msg, const size_t msg_len, uint8_t *digest) {
  sha256_state_t state;
  sha256_init(&state);

  // Process data with padding enabled.
  HARDENED_TRY(process_message(&state, msg, msg_len, kHardenedBoolTrue));

  // Retrieve the final digest and destroy the state.
  digest_get(&state, digest);
  state_shred(&state);
  return OTCRYPTO_OK;
}
