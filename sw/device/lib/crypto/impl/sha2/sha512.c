// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sha2/sha512.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', '2', '5')

enum {
  /**
   * Maximum number of message chunks that the OTBN app can accept.
   *
   * This number is based on the DMEM size limit and usage by the SHA-512 app
   * itself; see `run_sha512.s` for the detailed calculation.
   */
  kSha512MaxMessageChunksPerOtbnRun = 16,
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

// Initial state for SHA-384 (see FIPS 180-4, section 5.3.4).
static const uint32_t kSha384InitialState[] = {
    0xcbbb9d5d, 0xc1059ed8, 0x629a292a, 0x367cd507, 0x9159015a, 0x3070dd17,
    0x152fecd8, 0xf70e5939, 0x67332667, 0xffc00b31, 0x8eb44a87, 0x68581511,
    0xdb0c2e0d, 0x64f98fa7, 0x47b5481d, 0xbefa4fa4,
};

// Initial state for SHA-512 (see FIPS 180-4, section 5.3.5).
static const uint32_t kSha512InitialState[kSha512StateWords] = {
    0x6a09e667, 0xf3bcc908, 0xbb67ae85, 0x84caa73b, 0x3c6ef372, 0xfe94f82b,
    0xa54ff53a, 0x5f1d36f1, 0x510e527f, 0xade682d1, 0x9b05688c, 0x2b3e6c1f,
    0x1f83d9ab, 0xfb41bd6b, 0x5be0cd19, 0x137e2179,
};
static_assert(sizeof(kSha512InitialState) == kSha512StateBytes,
              "Initial state for SHA-512 has an unexpected size.");

OTBN_DECLARE_APP_SYMBOLS(run_sha512);            // The OTBN SHA-512 app.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, state);     // Hash state.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, msg);       // Input message.
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, n_chunks);  // Message length in blocks.

static const otbn_app_t kOtbnAppSha512 = OTBN_APP_T_INIT(run_sha512);
static const otbn_addr_t kOtbnVarSha512State =
    OTBN_ADDR_T_INIT(run_sha512, state);
static const otbn_addr_t kOtbnVarSha512Msg = OTBN_ADDR_T_INIT(run_sha512, msg);
static const otbn_addr_t kOtbnVarSha512NChunks =
    OTBN_ADDR_T_INIT(run_sha512, n_chunks);

void sha512_init(sha512_state_t *state) {
  // Set the initial state.
  hardened_memcpy(state->H, kSha512InitialState, kSha512StateWords);
  // Set the partial block to 0 (the value is ignored).
  memset(state->partial_block, 0, sizeof(state->partial_block));
  // Set the message length so far to 0.
  state->total_len.lower = 0;
  state->total_len.upper = 0;
}

void sha384_init(sha512_state_t *state) {
  // Set the initial state.
  hardened_memcpy(state->H, kSha384InitialState, kSha512StateWords);
  // Set the partial block to 0 (the value is ignored).
  memset(state->partial_block, 0, sizeof(state->partial_block));
  // Set the message length so far to 0.
  state->total_len.lower = 0;
  state->total_len.upper = 0;
}

/**
 * Calculate an updated total message length and check that it is acceptable.
 *
 * Returns `OTCRYPTO_BAD_ARGS` if the current message length plus the new
 * message length exceeds the SHA-512/SHA-384 maximum of 2^128 bits.
 *
 * This function is does not modify the state object; this is because in case
 * of OTBN errors partway through the operation, the state could get out of
 * sync.
 *
 * @param state Context object.
 * @param msg_len Length of new data in bytes.
 * @param[out] new_total_len New total received data length.
 * @return Result of the operation.
 */
static status_t get_new_total_len(const sha512_state_t *state, size_t msg_len,
                                  sha512_message_length_t *new_total_len) {
  // We need to shift `msg_len` here because `total_len` is in bits, not bytes.
  new_total_len->lower = state->total_len.lower + (msg_len << 3);
  new_total_len->upper = state->total_len.upper;
  if (new_total_len->lower < state->total_len.lower) {
    // If we got here, the addition for the first limb overflowed; add 1 to the
    // next limb.
    new_total_len->upper += 1;
  }
  if (new_total_len->upper < state->total_len.upper) {
    // If the second subtraction overflowed, then the message is too long for
    // SHA-512.
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Pad the block as described in FIPS 180-4, section 5.1.2.
 *
 * Padding fills the current block and may require one additional block.
 *
 * The length of real data in the partial block should be the byte-length of
 * the message so far (total_len >> 3) modulo `kSha512MessageBlockBytes`.
 *
 * @param total_len Total length of message so far.
 * @param block Current (partial) block, updated in-place.
 * @param[out] additional_block Buffer for an additional padding block.
 * @return Length of padding added in bytes.
 * @return Result of the operation.
 */
static size_t add_padding(const sha512_message_length_t total_len,
                          sha512_message_block_t *block,
                          sha512_message_block_t *additional_block) {
  size_t partial_block_len = (total_len.lower >> 3) % kSha512MessageBlockBytes;

  // Get a byte-sized pointer to the end of the real data within the block.
  unsigned char *data_end = (unsigned char *)block->data + partial_block_len;

  // Fill the remainder of the block with zeroes.
  size_t padding_len = kSha512MessageBlockBytes - partial_block_len;
  memset(data_end, 0, padding_len);

  // Set the last byte after the message to 0x80. There must be at least one
  // unfilled byte in the partial block, since partial_block_len is always <
  // kSha512MessageBlockBytes.
  memset(data_end, 0x80, 1);

  sha512_message_block_t *final_block = block;
  if (partial_block_len + 1 + 2 * sizeof(uint64_t) > kSha512MessageBlockBytes) {
    // We need the additional block; partial data + 0x80 + 16-byte encoding of
    // length will not fit in the current block.
    memset(additional_block, 0, kSha512MessageBlockBytes);
    padding_len += kSha512MessageBlockBytes;
    final_block = additional_block;
  }

  // Set the last 128 bits (=4 32b words) of the final block to the bit-length
  // in big-endian form.
  final_block->data[kSha512MessageBlockWords - 1] =
      __builtin_bswap32(total_len.lower & UINT32_MAX);
  final_block->data[kSha512MessageBlockWords - 2] =
      __builtin_bswap32(total_len.lower >> 32);
  final_block->data[kSha512MessageBlockWords - 3] =
      __builtin_bswap32(total_len.upper & UINT32_MAX);
  final_block->data[kSha512MessageBlockWords - 4] =
      __builtin_bswap32(total_len.upper >> 32);
  return padding_len;
}

/**
 * Run OTBN to process the data currently in DMEM.
 *
 * @param ctx OTBN message buffer context information (updated in place).
 * @return Result of the operation.
 */
static status_t process_message_buffer(sha512_otbn_ctx_t *ctx) {
  // Write the number of blocks to DMEM.
  HARDENED_TRY(otbn_dmem_write(1, &ctx->num_blocks, kOtbnVarSha512NChunks));

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
static status_t process_block(sha512_otbn_ctx_t *ctx,
                              const sha512_message_block_t *block) {
  // Calculate the offset within the message buffer.
  size_t offset = ctx->num_blocks * kSha512MessageBlockBytes;
  otbn_addr_t dst = kOtbnVarSha512Msg + offset;

  // Copy the message block into DMEM. The SHA-512 app expects 64-bit words
  // within the message in big-endian form, so we copy 64 bits at a time and
  // swap the order.
  for (size_t i = 0; i + 1 < kSha512MessageBlockWords; i += 2) {
    uint32_t bytes_7to4 = __builtin_bswap32(block->data[i + 1]);
    uint32_t bytes_3to0 = __builtin_bswap32(block->data[i]);
    HARDENED_TRY(otbn_dmem_write(1, &bytes_7to4, dst));
    dst += sizeof(uint32_t);
    HARDENED_TRY(otbn_dmem_write(1, &bytes_3to0, dst));
    dst += sizeof(uint32_t);
  }
  ctx->num_blocks += 1;

  // If we've reached the maximum number of message chunks for a single run,
  // then run the OTBN program to update the state in-place. Note that there
  // is no need to read back and then re-write the state; it'll stay updated
  // in DMEM for the next run.
  if (ctx->num_blocks == kSha512MaxMessageChunksPerOtbnRun) {
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
static status_t process_message(sha512_state_t *state, const uint8_t *msg,
                                size_t msg_len,
                                hardened_bool_t padding_needed) {
  // Load the SHA-512 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppSha512));

  // Calculate the new value of state->total_len. Do NOT update the state yet
  // (because if we get an OTBN error, it would become out of sync).
  sha512_state_t new_state;
  HARDENED_TRY(get_new_total_len(state, msg_len, &new_state.total_len));

  // Set the initial state. The OTBN app expects the state in a pre-processed
  // format, with the 64-bit state words aligned to wide-word boundaries.
  otbn_addr_t state_write_addr = kOtbnVarSha512State;
  for (size_t i = 0; i + 1 < kSha512StateWords; i += 2) {
    HARDENED_TRY(otbn_dmem_write(1, &state->H[i + 1], state_write_addr));
    HARDENED_TRY(
        otbn_dmem_write(1, &state->H[i], state_write_addr + sizeof(uint32_t)));
    state_write_addr += kOtbnWideWordNumBytes;
  }

  // Start computing the first block for the hash computation by simply copying
  // the partial block. We won't use the partial block directly to avoid
  // contaminating the context object if this operation fails later.
  sha512_message_block_t block;
  size_t partial_block_len =
      (state->total_len.lower >> 3) % kSha512MessageBlockBytes;
  hardened_memcpy(block.data, state->partial_block, kSha512MessageBlockWords);

  // Initialize the context for the OTBN message buffer.
  sha512_otbn_ctx_t ctx = {.num_blocks = 0};

  // Process the message one block at a time, including partial data if it is
  // present (which is only possible on the first iteration).
  while (msg_len >= kSha512MessageBlockBytes - partial_block_len) {
    size_t available_len = kSha512MessageBlockBytes - partial_block_len;
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
    sha512_message_block_t additional_block;
    size_t padding_len =
        add_padding(new_state.total_len, &block, &additional_block);
    // We always fill `block`; process it.
    HARDENED_TRY(process_block(&ctx, &block));
    // Check if `additional_block` was used, and process it if so.
    if (padding_len >= kSha512MessageBlockBytes) {
      HARDENED_TRY(process_block(&ctx, &additional_block));
    }
  }

  // If there are any unprocessed blocks currently in DMEM, run the program one
  // final time.
  if (ctx.num_blocks > 0) {
    HARDENED_TRY(process_message_buffer(&ctx));
  }

  // Read the final state from OTBN dmem. The state is still in the special
  // form the OTBN app uses, with the 64-bit state words aligned to wide-word
  // boundaries.
  otbn_addr_t state_read_addr = kOtbnVarSha512State;
  for (size_t i = 0; i + 1 < kSha512StateWords; i += 2) {
    HARDENED_TRY(otbn_dmem_read(1, state_read_addr, &new_state.H[i + 1]));
    HARDENED_TRY(
        otbn_dmem_read(1, state_read_addr + sizeof(uint32_t), &new_state.H[i]));
    state_read_addr += kOtbnWideWordNumBytes;
  }

  // Clear OTBN's memory.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  // At this point, no more errors are possible; it is safe to update the
  // context object.
  hardened_memcpy(state->H, new_state.H, kSha512StateWords);
  hardened_memcpy(state->partial_block, block.data, kSha512MessageBlockWords);
  state->total_len.lower = new_state.total_len.lower;
  state->total_len.upper = new_state.total_len.upper;
  return OTCRYPTO_OK;
}

status_t sha512_update(sha512_state_t *state, const uint8_t *msg,
                       const size_t msg_len) {
  // Process new data with no padding.
  return process_message(state, msg, msg_len, kHardenedBoolFalse);
}

/**
 * Replace sensitive data in a SHA-512 context with non-sensitive values.
 *
 * @param state The context object to shred.
 */
static void state_shred(sha512_state_t *state) {
  hardened_memshred(state->H, kSha512StateWords);
  hardened_memshred(state->partial_block, kSha512MessageBlockWords);
  state->total_len.lower = 0;
  state->total_len.upper = 0;
}

/**
 * Copy the final SHA-512 digest as a byte-string.
 *
 * SHA-512 intermediate computations use words in little-endian format, but the
 * FIPS 180-4 spec requires big-endian words (see section 3.1). Therefore, to
 * get the right final byte-order, we need to reverse each word in the state.
 *
 * @param state Context object.
 * @param[out] digest Destination buffer for digest.
 */
static void sha512_digest_get(sha512_state_t *state, uint8_t *digest) {
  // Reverse the bytes in each word to match FIPS 180-4.
  for (size_t i = 0; i < kSha512StateWords; i++) {
    state->H[i] = __builtin_bswap32(state->H[i]);
  }
  // TODO(#17711): this can be `hardened_memcpy` if `digest` is aligned.
  memcpy(digest, state->H, kSha512DigestBytes);
}

/**
 * Copy the final SHA-384 digest as a byte-string.
 *
 * The SHA-384 digest is formed the same was as SHA-512, but truncated to 384
 * bits.
 *
 * @param state Context object.
 * @param[out] digest Destination buffer for digest.
 */
static void sha384_digest_get(sha512_state_t *state, uint8_t *digest) {
  // Reverse the bytes in each word to match FIPS 180-4.
  for (size_t i = 0; i < kSha512StateWords; i++) {
    state->H[i] = __builtin_bswap32(state->H[i]);
  }
  // TODO(#17711): this can be `hardened_memcpy` if `digest` is aligned.
  memcpy(digest, state->H, kSha384DigestBytes);
}

status_t sha512_final(sha512_state_t *state, uint8_t *digest) {
  // Construct padding.
  HARDENED_TRY(process_message(state, NULL, 0, kHardenedBoolTrue));

  // Copy the digest and then destroy the state.
  sha512_digest_get(state, digest);
  state_shred(state);
  return OTCRYPTO_OK;
}

status_t sha512(const uint8_t *msg, const size_t msg_len, uint8_t *digest) {
  sha512_state_t state;
  sha512_init(&state);

  // Process data with padding enabled.
  HARDENED_TRY(process_message(&state, msg, msg_len, kHardenedBoolTrue));
  sha512_digest_get(&state, digest);
  state_shred(&state);
  return OTCRYPTO_OK;
}

status_t sha384_update(sha384_state_t *state, const uint8_t *msg,
                       const size_t msg_len) {
  // An update for SHA-384 is exactly the same as for SHA-512.
  return sha512_update(state, msg, msg_len);
}

status_t sha384_final(sha384_state_t *state, uint8_t *digest) {
  // Construct padding.
  HARDENED_TRY(process_message(state, NULL, 0, kHardenedBoolTrue));

  // Copy the digest and then destroy the state.
  sha384_digest_get(state, digest);
  state_shred(state);
  return OTCRYPTO_OK;
}

status_t sha384(const uint8_t *msg, const size_t msg_len, uint8_t *digest) {
  sha384_state_t state;
  sha384_init(&state);

  // Process data with padding enabled.
  HARDENED_TRY(process_message(&state, msg, msg_len, kHardenedBoolTrue));
  sha384_digest_get(&state, digest);
  state_shred(&state);
  return OTCRYPTO_OK;
}
