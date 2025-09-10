// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'h', 'm')

OT_ASSERT_ENUM_VALUE(HMAC_KEY_1_REG_OFFSET, HMAC_KEY_0_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_2_REG_OFFSET, HMAC_KEY_1_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_3_REG_OFFSET, HMAC_KEY_2_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_4_REG_OFFSET, HMAC_KEY_3_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_5_REG_OFFSET, HMAC_KEY_4_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_6_REG_OFFSET, HMAC_KEY_5_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_7_REG_OFFSET, HMAC_KEY_6_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_8_REG_OFFSET, HMAC_KEY_7_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_9_REG_OFFSET, HMAC_KEY_8_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_10_REG_OFFSET, HMAC_KEY_9_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_11_REG_OFFSET, HMAC_KEY_10_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_12_REG_OFFSET, HMAC_KEY_11_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_13_REG_OFFSET, HMAC_KEY_12_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_14_REG_OFFSET, HMAC_KEY_13_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_15_REG_OFFSET, HMAC_KEY_14_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_16_REG_OFFSET, HMAC_KEY_15_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_17_REG_OFFSET, HMAC_KEY_16_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_18_REG_OFFSET, HMAC_KEY_17_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_19_REG_OFFSET, HMAC_KEY_18_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_20_REG_OFFSET, HMAC_KEY_19_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_21_REG_OFFSET, HMAC_KEY_20_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_22_REG_OFFSET, HMAC_KEY_21_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_23_REG_OFFSET, HMAC_KEY_22_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_24_REG_OFFSET, HMAC_KEY_23_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_25_REG_OFFSET, HMAC_KEY_24_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_26_REG_OFFSET, HMAC_KEY_25_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_27_REG_OFFSET, HMAC_KEY_26_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_28_REG_OFFSET, HMAC_KEY_27_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_29_REG_OFFSET, HMAC_KEY_28_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_30_REG_OFFSET, HMAC_KEY_29_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_KEY_31_REG_OFFSET, HMAC_KEY_30_REG_OFFSET + 4);

OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_1_REG_OFFSET, HMAC_DIGEST_0_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_2_REG_OFFSET, HMAC_DIGEST_1_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_3_REG_OFFSET, HMAC_DIGEST_2_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_4_REG_OFFSET, HMAC_DIGEST_3_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_5_REG_OFFSET, HMAC_DIGEST_4_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_6_REG_OFFSET, HMAC_DIGEST_5_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_7_REG_OFFSET, HMAC_DIGEST_6_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_8_REG_OFFSET, HMAC_DIGEST_7_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_9_REG_OFFSET, HMAC_DIGEST_8_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_10_REG_OFFSET, HMAC_DIGEST_9_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_11_REG_OFFSET, HMAC_DIGEST_10_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_12_REG_OFFSET, HMAC_DIGEST_11_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_13_REG_OFFSET, HMAC_DIGEST_12_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_14_REG_OFFSET, HMAC_DIGEST_13_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(HMAC_DIGEST_15_REG_OFFSET, HMAC_DIGEST_14_REG_OFFSET + 4);

enum {
  /* The beginning of the address space of HMAC. */
  kHmacBaseAddr = TOP_EARLGREY_HMAC_BASE_ADDR,
  /* Timeout value for the polling
   * As min 3 clock cycles are required to perform a read access to the STATUS
   * hmac_idle register. And as we should observe 240 cycles (80 for the inner
   * key, 80 for the outer key, and 80 for the result of the first round), plus
   * 80 for msg itself -> 360 cycles in total as max (when HMAC is enabled).
   * Which means, 360/3=120 loops before having the IDLE state.
   * Let's take a large margin and consider that 200 loops are enough.
   */
  kNumIterTimeout = 200,
};

/**
 * Digest size selector values.
 *
 * These values can be directly written into the configuration register.
 */
typedef enum hmac_digest_length {
  kDigestLengthSha256 = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256,
  kDigestLengthSha384 = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_384,
  kDigestLengthSha512 = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512,
} hmac_digest_length_t;

/**
 * Key length selector values.
 *
 * These values can be directly written into the configuration register.
 *
 * As per the HMAC documentation, the key length can also be between these
 * values; in this case, select the next size up and pad with zeroes.
 */
typedef enum hmac_key_length {
  kKeyLength128 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_128,
  kKeyLength256 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_256,
  kKeyLength384 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_384,
  kKeyLength512 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_512,
  kKeyLength1024 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_1024,
  kKeyLengthNone = HMAC_CFG_KEY_LENGTH_VALUE_KEY_NONE,
} hmac_key_length_t;

/**
 * Wait until HMAC becomes idle.
 *
 * It returns error if HMAC HWIP becomes idle without firing `hmac_done`
 * interrupt.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t hmac_idle_wait(void) {
  // Initialize `status = 0` so that the loop starts with the assumption
  // that HMAC is not idle.
  uint32_t status = 0;
  uint32_t attempt_cnt = 0;
  while (bitfield_bit32_read(status, HMAC_STATUS_HMAC_IDLE_BIT) == 0) {
    status = abs_mmio_read32(kHmacBaseAddr + HMAC_STATUS_REG_OFFSET);
    attempt_cnt++;
    if (attempt_cnt >= kNumIterTimeout) {
      return OTCRYPTO_FATAL_ERR;
    }
  }

  // Verify that HMAC HWIP raises `hmac_done` bit.
  uint32_t intr_state =
      abs_mmio_read32(kHmacBaseAddr + HMAC_INTR_STATE_REG_OFFSET);
  if (bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT) == 0) {
    return OTCRYPTO_FATAL_ERR;
  }

  // Clear the interrupt by writing 1, because `INTR_STATE` is rw1c type.
  abs_mmio_write32(kHmacBaseAddr + HMAC_INTR_STATE_REG_OFFSET, intr_state);
  return OTCRYPTO_OK;
}

/**
 * Clear the state of HMAC HWIP so that further driver calls can use it.
 *
 * This function cannot force stop HMAC HWIP, and ongoing operations will not
 * simply stop by deasserting `sha_en` bit. Instead it should be used after
 * HMAC HWIP indicates that it is idle (see `hmac_idle_wait`).
 *
 * It also clears the internal state of HMAC HWIP by overwriting sensitive
 * values with 1s.
 *
 * @return Result of the operation.
 */
static status_t clear(void) {
  // Do not clear the config yet, we just need to deassert sha_en, see #23014.
  uint32_t cfg = abs_mmio_read32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg);

  // Use a random value from EDN to wipe HMAC.
  abs_mmio_write32(kHmacBaseAddr + HMAC_WIPE_SECRET_REG_OFFSET,
                   (uint32_t)ibex_rnd32_read());
  return OTCRYPTO_OK;
}

/**
 * Write given key to HMAC HWIP.
 *
 * This function does not return error, so it is the responsibility of the
 * caller to check that `key` and `key_len` are correctly set. Moreover, the
 * caller must ensure that HMAC HWIP is in an idle state that accepts writing
 * key words.
 *
 * The key may be NULL if `key_wordlen` is zero; in that case this function is
 * a no-op.
 *
 * @param key The buffer that points to the key.
 * @param key_wordlen The length of the key in words.
 * @return Result of the operation.
 */
static status_t key_write(const uint32_t *key, size_t key_wordlen) {
  uint32_t key_reg = kHmacBaseAddr + HMAC_KEY_0_REG_OFFSET;
  hardened_memcpy((uint32_t *)key_reg, key, key_wordlen);

  return OTCRYPTO_OK;
}

/**
 * Copy the digest result from HMAC HWIP to given `digest` buffer.
 *
 * This function does not return error, so it is the responsibility of the
 * caller to check that `digest` and `digest_wordlen` are correctly set.
 * Moreover, the caller must ensure that HMAC HWIP is in a state that permits
 * reading the digest value, that is, either of stop or process commands is
 * issued.
 *
 * @param[out] digest The digest buffer to copy to the result.
 * @param digest_wordlen The length of the digest buffer in words.
 */
static void digest_read(uint32_t *digest, size_t digest_wordlen) {
  for (size_t i = 0; i < digest_wordlen; i++) {
    digest[i] = abs_mmio_read32(kHmacBaseAddr + HMAC_DIGEST_0_REG_OFFSET +
                                sizeof(uint32_t) * i);
  }
}

/**
 * Resume a streaming operation from a saved context.
 *
 * @param ctx Context object from which to restore.
 * @return Result of the operation.
 */
static status_t context_restore(hmac_ctx_t *ctx) {
  // The previous caller should have left it clean, but it doesn't hurt to
  // clear again.
  HARDENED_TRY(clear());

  // Restore CFG register from `ctx->cfg_reg`. We need to keep `sha_en` low
  // until context is restored, see #23014.
  uint32_t cfg = bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg);

  // Write to KEY registers for HMAC operations. If the operation is SHA-2,
  // `key_wordlen` is set to 0 during `ctx` initialization.
  HARDENED_TRY(key_write(ctx->key, ctx->key_wordlen));

  uint32_t cmd = HMAC_CMD_REG_RESVAL;
  // Decide if we need to invoke `start` or `continue` command.
  if (ctx->upper == 0 && ctx->lower == 0) {
    cmd = bitfield_bit32_write(cmd, HMAC_CMD_HASH_START_BIT, 1);
  } else {
    cmd = bitfield_bit32_write(cmd, HMAC_CMD_HASH_CONTINUE_BIT, 1);

    // For SHA-256 and HMAC-256, we do not need to write to the second half of
    // DIGEST registers, but we do it anyway to keep the driver simple.
    size_t i = 0;
    for (; launder32(i) < kHmacMaxDigestWords; i++) {
      abs_mmio_write32(
          kHmacBaseAddr + HMAC_DIGEST_0_REG_OFFSET + sizeof(uint32_t) * i,
          ctx->H[i]);
    }
    // Check that the loop ran for the correct number of iterations.
    HARDENED_CHECK_EQ(i, kHmacMaxDigestWords);
    abs_mmio_write32(kHmacBaseAddr + HMAC_MSG_LENGTH_LOWER_REG_OFFSET,
                     ctx->lower);
    abs_mmio_write32(kHmacBaseAddr + HMAC_MSG_LENGTH_UPPER_REG_OFFSET,
                     ctx->upper);
  }

  // We could not set `sha_en` before updating context registers (see #23014).
  // Now that context registers are restored, enable `sha_en`.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg);

  // Now we can finally write the command to the register to actually issue
  // `start` or `continue`.
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd);

  return OTCRYPTO_OK;
}

/**
 * Save the context from HMAC HWIP into `ctx` object.
 *
 * This function should be called only after `stop` command is invoked and
 * HMAC HWIP is idle.
 *
 * @param[out] ctx Context to which values are written.
 */
static void context_save(hmac_ctx_t *ctx) {
  // For SHA-256 and HMAC-256, we do not need to save to the second half of
  // DIGEST registers, but we do it anyway to keep the driver simple.
  digest_read(ctx->H, kHmacMaxDigestWords);
  ctx->lower =
      abs_mmio_read32(kHmacBaseAddr + HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  ctx->upper =
      abs_mmio_read32(kHmacBaseAddr + HMAC_MSG_LENGTH_UPPER_REG_OFFSET);
}

/**
 * Wipes the ctx struct by replacing sensitive data with randomness from the
 * Ibex EDN interface. Non-sensitive variables are zeroized.
 *
 * @param[out] ctx Initialized context object for SHA2/HMAC-SHA2 operations.
 * @return Result of the operation.
 */
static status_t hmac_context_wipe(hmac_ctx_t *ctx) {
  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Randomize sensitive data.
  hardened_memshred(ctx->key, kHmacMaxBlockWords);
  hardened_memshred(ctx->H, kHmacMaxDigestWords);
  hardened_memshred((uint32_t *)(ctx->partial_block),
                    kHmacMaxBlockBytes / sizeof(uint32_t));
  // Zero the remaining ctx fields.
  ctx->cfg_reg = 0;
  ctx->key_wordlen = 0;
  ctx->msg_block_wordlen = 0;
  ctx->digest_wordlen = 0;
  ctx->lower = 0;
  ctx->upper = 0;
  ctx->partial_block_bytelen = 0;

  return OTCRYPTO_OK;
}

/**
 * Write given byte array into the `MSG_FIFO`. This function should only be
 * called when HMAC HWIP is already running and expecting further message bytes.
 *
 * @param message The incoming message buffer to be fed into HMAC_FIFO.
 * @param message_len The length of `message` in bytes.
 * @return Result of the operation.
 */
static status_t msg_fifo_write(const uint8_t *message, size_t message_len) {
  // TODO(#23191): Should we handle backpressure here?
  // Begin by writing a one byte at a time until the data is aligned.
  size_t i = 0;
  for (; misalignment32_of((uintptr_t)(&message[i])) > 0 &&
         launder32(i) < message_len;
       i++) {
    abs_mmio_write8(kHmacBaseAddr + HMAC_MSG_FIFO_REG_OFFSET, message[i]);
  }

  // Write one word at a time as long as there is a full word available.
  for (; launder32(i + sizeof(uint32_t)) <= message_len;
       i += sizeof(uint32_t)) {
    uint32_t next_word = read_32(&message[i]);
    abs_mmio_write32(kHmacBaseAddr + HMAC_MSG_FIFO_REG_OFFSET, next_word);
  }

  // For the last few bytes, we need to write one byte at a time again.
  for (; launder32(i) < message_len; i++) {
    abs_mmio_write8(kHmacBaseAddr + HMAC_MSG_FIFO_REG_OFFSET, message[i]);
  }
  // Check that the loops ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, message_len);

  return OTCRYPTO_OK;
}

/**
 * Determine the HMAC block configuration register.
 *
 * @param hmac_en Whether to enable HMAC (false for hashing only).
 * @param digest_len Digest length selector.
 * @param key_len Key length selector.
 * @return Configuration register.
 */
static uint32_t cfg_get(bool hmac_en, hmac_digest_length_t digest_len,
                        hmac_key_length_t key_len) {
  uint32_t cfg = HMAC_CFG_REG_RESVAL;
  // The endianness is fixed at driver level and not exposed to the caller.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_KEY_SWAP_BIT, true);

  // Digest should be big-endian to match the SHA-256 specification.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, true);

  // Message should be little-endian to match Ibex's endianness.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);

  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, hmac_en);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_KEY_LENGTH_FIELD, key_len);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_DIGEST_SIZE_FIELD, digest_len);
  return cfg;
}

/**
 * Checks that the HMAC block is idle and returns an error otherwise.
 *
 * @return OK if the block is idle, OTCRYPTO_RECOV_ERR otherwise.
 */
static status_t ensure_idle(void) {
  uint32_t status = abs_mmio_read32(kHmacBaseAddr + HMAC_STATUS_REG_OFFSET);
  if (bitfield_bit32_read(status, HMAC_STATUS_HMAC_IDLE_BIT) == 0) {
    return OTCRYPTO_RECOV_ERR;
  }
  return OTCRYPTO_OK;
}

/**
 * One-shot HMAC block operation.
 *
 * Configures the block, sends the START command, processes the message, and
 * reads the digest.
 *
 * @param cfg HMAC block configuration register.
 * @param key Key input for HMAC (may be NULL if `key_wordlen` is 0).
 * @param key_wordlen Length of key input in words.
 * @param msg Message data.
 * @param msg_len Length of message data in bytes.
 * @param digest_wordlen Digest length in 32-bit words.
 * @param[out] digest Buffer for the digest.
 */
static status_t oneshot(const uint32_t cfg, const uint32_t *key,
                        size_t key_wordlen, const uint8_t *msg, size_t msg_len,
                        size_t digest_wordlen, uint32_t *digest) {
  // Check that the block is idle.
  HARDENED_TRY(ensure_idle());

  // Make sure that the entropy complex is configured correctly.
  HARDENED_TRY(entropy_complex_check());

  // Configure the HMAC block.
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg);

  // Write the key (no-op if the key length is 0, e.g. for hashing).
  HARDENED_TRY(key_write(key, key_wordlen));

  // Read back the HMAC configuration and compare to the expected configuration.
  HARDENED_CHECK_EQ(abs_mmio_read32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET),
                    launder32(cfg));

  // Send the START command.
  uint32_t cmd =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_START_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd);

  // Write the message.
  HARDENED_TRY(msg_fifo_write(msg, msg_len));

  // Send the PROCESS command.
  cmd = bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_PROCESS_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for the digest to be ready, then read it.
  HARDENED_TRY(hmac_idle_wait());
  digest_read(digest, digest_wordlen);

  HARDENED_TRY(clear());
  return OTCRYPTO_OK;
}

status_t hmac_hash_sha256(const uint8_t *msg, size_t msg_len,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha256, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, /*key_wordlen=*/0, msg, msg_len,
                 kHmacSha256DigestWords, digest);
}

status_t hmac_hash_sha384(const uint8_t *msg, size_t msg_len,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha384, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, /*key_wordlen=*/0, msg, msg_len,
                 kHmacSha384DigestWords, digest);
}

status_t hmac_hash_sha512(const uint8_t *msg, size_t msg_len,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha512, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, /*key_wordlen=*/0, msg, msg_len,
                 kHmacSha512DigestWords, digest);
}

status_t hmac_hmac_sha256(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha256, kKeyLength512);
  return oneshot(cfg, key_block, kHmacSha256BlockWords, msg, msg_len,
                 kHmacSha256DigestWords, tag);
}

status_t hmac_hmac_sha256_redundant(const uint32_t *key_block,
                                    const uint8_t *msg, size_t msg_len,
                                    uint32_t *tag) {
  uint32_t o_key_pad[kHmacSha256BlockWords];
  uint32_t i_key_pad[kHmacSha256BlockWords];
  memset(o_key_pad, 0, kHmacSha256BlockBytes);
  memset(i_key_pad, 0, kHmacSha256BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  for (size_t it = 0; it < kHmacSha256BlockWords; it++) {
    o_key_pad[it] = key_block[it] ^ 0x5c5c5c5c;
    i_key_pad[it] = key_block[it] ^ 0x36363636;
  }

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg[kHmacSha256BlockBytes + msg_len];
  memset(i_key_pad_msg, 0, sizeof(i_key_pad_msg));
  memcpy(i_key_pad_msg, i_key_pad, kHmacSha256BlockBytes);
  memcpy(i_key_pad_msg + kHmacSha256BlockBytes, msg, msg_len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha256DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha256(i_key_pad_msg, kHmacSha256BlockBytes + msg_len,
                                h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash[kHmacSha256BlockBytes + kHmacSha256DigestBytes];
  memset(o_key_pad_hash, 0, sizeof(o_key_pad_hash));
  memcpy(o_key_pad_hash, o_key_pad, kHmacSha256BlockBytes);
  memcpy(o_key_pad_hash + kHmacSha256BlockBytes, h_i_key_pad_msg,
         kHmacSha256DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha256(o_key_pad_hash,
                          kHmacSha256BlockBytes + kHmacSha256DigestBytes, tag);
}

status_t hmac_hmac_sha384(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha384, kKeyLength1024);
  return oneshot(cfg, key_block, kHmacSha384BlockWords, msg, msg_len,
                 kHmacSha384DigestWords, tag);
}

status_t hmac_hmac_sha384_redundant(const uint32_t *key_block,
                                    const uint8_t *msg, size_t msg_len,
                                    uint32_t *tag) {
  uint32_t o_key_pad[kHmacSha384BlockWords];
  uint32_t i_key_pad[kHmacSha384BlockWords];
  memset(o_key_pad, 0, kHmacSha384BlockBytes);
  memset(i_key_pad, 0, kHmacSha384BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  for (size_t it = 0; it < kHmacSha384BlockWords; it++) {
    o_key_pad[it] = key_block[it] ^ 0x5c5c5c5c;
    i_key_pad[it] = key_block[it] ^ 0x36363636;
  }

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg[kHmacSha384BlockBytes + msg_len];
  memset(i_key_pad_msg, 0, sizeof(i_key_pad_msg));
  memcpy(i_key_pad_msg, i_key_pad, kHmacSha384BlockBytes);
  memcpy(i_key_pad_msg + kHmacSha384BlockBytes, msg, msg_len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha384DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha384(i_key_pad_msg, kHmacSha384BlockBytes + msg_len,
                                h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash[kHmacSha384BlockBytes + kHmacSha384DigestBytes];
  memset(o_key_pad_hash, 0, sizeof(o_key_pad_hash));
  memcpy(o_key_pad_hash, o_key_pad, kHmacSha384BlockBytes);
  memcpy(o_key_pad_hash + kHmacSha384BlockBytes, h_i_key_pad_msg,
         kHmacSha384DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha384(o_key_pad_hash,
                          kHmacSha384BlockBytes + kHmacSha384DigestBytes, tag);
}

status_t hmac_hmac_sha512(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha512, kKeyLength1024);
  return oneshot(cfg, key_block, kHmacSha512BlockWords, msg, msg_len,
                 kHmacSha512DigestWords, tag);
}

status_t hmac_hmac_sha512_redundant(const uint32_t *key_block,
                                    const uint8_t *msg, size_t msg_len,
                                    uint32_t *tag) {
  uint32_t o_key_pad[kHmacSha512BlockWords];
  uint32_t i_key_pad[kHmacSha512BlockWords];
  memset(o_key_pad, 0, kHmacSha512BlockBytes);
  memset(i_key_pad, 0, kHmacSha512BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  for (size_t it = 0; it < kHmacSha512BlockWords; it++) {
    o_key_pad[it] = key_block[it] ^ 0x5c5c5c5c;
    i_key_pad[it] = key_block[it] ^ 0x36363636;
  }

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg[kHmacSha512BlockBytes + msg_len];
  memset(i_key_pad_msg, 0, sizeof(i_key_pad_msg));
  memcpy(i_key_pad_msg, i_key_pad, kHmacSha512BlockBytes);
  memcpy(i_key_pad_msg + kHmacSha512BlockBytes, msg, msg_len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha512DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha512(i_key_pad_msg, kHmacSha512BlockBytes + msg_len,
                                h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash[kHmacSha512BlockBytes + kHmacSha512DigestBytes];
  memset(o_key_pad_hash, 0, sizeof(o_key_pad_hash));
  memcpy(o_key_pad_hash, o_key_pad, kHmacSha512BlockBytes);
  memcpy(o_key_pad_hash + kHmacSha512BlockBytes, h_i_key_pad_msg,
         kHmacSha512DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha512(o_key_pad_hash,
                          kHmacSha512BlockBytes + kHmacSha512DigestBytes, tag);
}

/**
 * Initialize the context for a hashing operation.
 *
 * The `msg_block_wordlen` and `digest_wordlen` fields of `ctx` is not set by
 * this operation.
 *
 * @param key Key data for HMAC.
 * @param key_wordlen Length of the key in words.
 * @param digest_len Digest length selector.
 * @param[out] ctx Initialized context object.
 */
static void sha2_init(hmac_digest_length_t digest_len, hmac_ctx_t *ctx) {
  ctx->cfg_reg = cfg_get(/*hmac_en=*/false, digest_len, kKeyLengthNone);
  ctx->key_wordlen = 0;
  ctx->lower = 0;
  ctx->upper = 0;
  ctx->partial_block_bytelen = 0;
}

/**
 * Initialize the context for an HMAC operation.
 *
 * The `msg_block_wordlen`, `digest_wordlen`, `key`, and `key_wordlen` fields
 * of `ctx` are not set by this operation.
 *
 * @param key_len Key length selector.
 * @param digest_len Digest length selector.
 * @param[out] ctx Initialized context object.
 */
static void hmac_init(hmac_key_length_t key_len,
                      hmac_digest_length_t digest_len, hmac_ctx_t *ctx) {
  ctx->cfg_reg = cfg_get(/*hmac_en=*/true, digest_len, key_len);
  ctx->lower = 0;
  ctx->upper = 0;
  ctx->partial_block_bytelen = 0;
}

void hmac_hash_sha256_init(hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha256BlockWords,
  ctx->digest_wordlen = kHmacSha256DigestWords,
  sha2_init(kDigestLengthSha256, ctx);
}

void hmac_hash_sha384_init(hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha384BlockWords,
  ctx->digest_wordlen = kHmacSha384DigestWords,
  sha2_init(kDigestLengthSha384, ctx);
}

void hmac_hash_sha512_init(hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha512BlockWords,
  ctx->digest_wordlen = kHmacSha512DigestWords,
  sha2_init(kDigestLengthSha512, ctx);
}

void hmac_hmac_sha256_init(const uint32_t *key_block, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha256BlockWords,
  ctx->digest_wordlen = kHmacSha256DigestWords,
  ctx->key_wordlen = kHmacSha256BlockWords;
  memcpy(ctx->key, key_block, ctx->key_wordlen * sizeof(uint32_t));
  hmac_init(kKeyLength512, kDigestLengthSha256, ctx);
}

void hmac_hmac_sha384_init(const uint32_t *key_block, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha384BlockWords,
  ctx->digest_wordlen = kHmacSha384DigestWords,
  ctx->key_wordlen = kHmacSha384BlockWords;
  memcpy(ctx->key, key_block, ctx->key_wordlen * sizeof(uint32_t));
  hmac_init(kKeyLength1024, kDigestLengthSha384, ctx);
}

void hmac_hmac_sha512_init(const uint32_t *key_block, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha512BlockWords,
  ctx->digest_wordlen = kHmacSha512DigestWords,
  ctx->key_wordlen = kHmacSha512BlockWords;
  memcpy(ctx->key, key_block, ctx->key_wordlen * sizeof(uint32_t));
  hmac_init(kKeyLength1024, kDigestLengthSha512, ctx);
}

status_t hmac_update(hmac_ctx_t *ctx, const uint8_t *data, size_t len) {
  // Make sure that the entropy complex is configured correctly.
  HARDENED_TRY(entropy_complex_check());

  // If we don't have enough new bytes to fill a block, just update the partial
  // block and return.
  size_t block_bytelen = ctx->msg_block_wordlen * sizeof(uint32_t);
  if (len < block_bytelen - ctx->partial_block_bytelen) {
    memcpy((unsigned char *)(ctx->partial_block) + ctx->partial_block_bytelen,
           data, len);
    ctx->partial_block_bytelen += len;
    return OTCRYPTO_OK;
  }

  // Calculate the number of bytes that will be in the next partial block.
  // Reduce `len` modulo the block length preemptively to protect against
  // integer overflow when adding to the partial length.
  size_t len_rem = len % block_bytelen;
  size_t leftover_len = (ctx->partial_block_bytelen + len_rem) % block_bytelen;

  // Retore context will restore the context and also hit start or continue
  // button as necessary.
  HARDENED_TRY(context_restore(ctx));

  // Write the partial block, then the new bytes.
  HARDENED_TRY(msg_fifo_write((unsigned char *)ctx->partial_block,
                              ctx->partial_block_bytelen));
  HARDENED_TRY(msg_fifo_write(data, len - leftover_len));

  // Send the STOP command.
  uint32_t cmd =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_STOP_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for HMAC to be done, then store the context.
  HARDENED_TRY(hmac_idle_wait());
  context_save(ctx);

  // Write leftover bytes to `partial_block`, so that future update/final call
  // can feed them to HMAC HWIP.
  memcpy(ctx->partial_block, data + (len - leftover_len), leftover_len);
  ctx->partial_block_bytelen = leftover_len;

  // Clean up.
  HARDENED_TRY(clear());
  return OTCRYPTO_OK;
}

status_t hmac_final(hmac_ctx_t *ctx, uint32_t *digest) {
  // Make sure that the entropy complex is configured correctly.
  HARDENED_TRY(entropy_complex_check());

  // Retore context will restore the context and also hit start or continue
  // button as necessary.
  HARDENED_TRY(context_restore(ctx));

  // Feed the final leftover bytes to HMAC HWIP.
  HARDENED_TRY(msg_fifo_write((unsigned char *)ctx->partial_block,
                              ctx->partial_block_bytelen));

  // All message bytes are fed, now hit the process button.
  uint32_t cmd =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_PROCESS_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for HMAC to be done, then read the digest.
  HARDENED_TRY(hmac_idle_wait());
  digest_read(digest, ctx->digest_wordlen);

  // Destroy sensitive values in the ctx object.
  HARDENED_TRY(hmac_context_wipe(ctx));

  // Clean up.
  HARDENED_TRY(clear());
  return OTCRYPTO_OK;
}
