// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "hw/top/dt/hmac.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top/hmac_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'h', 'm')

static const dt_hmac_t kHmacDt = kDtHmac;

static inline uint32_t hmac_base(void) {
  return dt_hmac_primary_reg_block(kHmacDt);
}

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
  const uint32_t kBase = hmac_base();
  while (bitfield_bit32_read(status, HMAC_STATUS_HMAC_IDLE_BIT) == 0) {
    status = abs_mmio_read32(kBase + HMAC_STATUS_REG_OFFSET);
    attempt_cnt++;
    if (attempt_cnt >= kNumIterTimeout) {
      return OTCRYPTO_FATAL_ERR;
    }
  }

  // Verify that HMAC HWIP raises `hmac_done` bit.
  uint32_t intr_state = abs_mmio_read32(kBase + HMAC_INTR_STATE_REG_OFFSET);
  if (bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT) == 0) {
    return OTCRYPTO_FATAL_ERR;
  }

  // Clear the interrupt by writing 1, because `INTR_STATE` is rw1c type.
  abs_mmio_write32(kBase + HMAC_INTR_STATE_REG_OFFSET, intr_state);
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
  uint32_t cfg = abs_mmio_read32(hmac_base() + HMAC_CFG_REG_OFFSET);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(hmac_base() + HMAC_CFG_REG_OFFSET, cfg);

  // Use a random value from EDN to wipe HMAC.
  abs_mmio_write32(hmac_base() + HMAC_WIPE_SECRET_REG_OFFSET,
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
 * The key may be NULL.
 *
 * @param key The buffer that points to the hmac_key_t key structure.
 * @return Result of the operation.
 */
static status_t key_write(const hmac_key_t *key) {
  if (key != NULL) {
    uint32_t key_reg = hmac_base() + HMAC_KEY_0_REG_OFFSET;
    HARDENED_TRY(
        hardened_memcpy((uint32_t *)key_reg, key->key_block, key->key_len));
    // We only check the integrity of the key when entering the CryptoLib. This
    // check here will catch any manipulations of the key or the pointer to the
    // key that might have happend in the meanwhile. We do it at this point as
    // the key just got written into the HMAC core in the `hardened_memcpy()`
    // above.
    if (launder32(key->key_len) != 0) {
      HARDENED_CHECK_EQ(hmac_key_integrity_checksum_check(key),
                        kHardenedBoolTrue);
    } else {
      HARDENED_CHECK_EQ(key->key_len, 0);
    }
  } else {
    HARDENED_CHECK_EQ(key, NULL);
  }

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
  const uint32_t kBase = hmac_base();
  for (size_t i = 0; i < digest_wordlen; i++) {
    digest[i] = abs_mmio_read32(kBase + HMAC_DIGEST_0_REG_OFFSET +
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

  const uint32_t kBase = hmac_base();

  // Restore CFG register from `ctx->cfg_reg`. We need to keep `sha_en` low
  // until context is restored, see #23014.
  uint32_t cfg = bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(kBase + HMAC_CFG_REG_OFFSET, cfg);

  // Write to KEY registers for HMAC operations. If the operation is SHA-2,
  // `key_wordlen` is set to 0 during `ctx` initialization.
  HARDENED_TRY(key_write(&ctx->key));

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
      abs_mmio_write32(kBase + HMAC_DIGEST_0_REG_OFFSET + sizeof(uint32_t) * i,
                       ctx->H[i]);
    }
    // Check that the loop ran for the correct number of iterations.
    HARDENED_CHECK_EQ(i, kHmacMaxDigestWords);
    abs_mmio_write32(kBase + HMAC_MSG_LENGTH_LOWER_REG_OFFSET, ctx->lower);
    abs_mmio_write32(kBase + HMAC_MSG_LENGTH_UPPER_REG_OFFSET, ctx->upper);
  }

  // We could not set `sha_en` before updating context registers (see #23014).
  // Now that context registers are restored, enable `sha_en`.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  abs_mmio_write32(kBase + HMAC_CFG_REG_OFFSET, cfg);

  // Now we can finally write the command to the register to actually issue
  // `start` or `continue`.
  abs_mmio_write32(kBase + HMAC_CMD_REG_OFFSET, cmd);

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
  ctx->lower = abs_mmio_read32(hmac_base() + HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  ctx->upper = abs_mmio_read32(hmac_base() + HMAC_MSG_LENGTH_UPPER_REG_OFFSET);
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
  HARDENED_TRY(hardened_memshred(ctx->key.key_block, kHmacMaxBlockWords));
  HARDENED_TRY(hardened_memshred(ctx->H, kHmacMaxDigestWords));
  HARDENED_TRY(hardened_memshred((uint32_t *)(ctx->partial_block),
                                 kHmacMaxBlockBytes / sizeof(uint32_t)));
  // Zero the remaining ctx fields.
  ctx->cfg_reg = 0;
  ctx->key.key_len = 0;
  ctx->key.checksum = 0;
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
  const uint32_t kBase = hmac_base();
  for (; misalignment32_of((uintptr_t)(&message[i])) > 0 &&
         launder32(i) < message_len;
       i++) {
    abs_mmio_write8(kBase + HMAC_MSG_FIFO_REG_OFFSET, message[i]);
  }

  // Write one word at a time as long as there is a full word available.
  for (; launder32(i + sizeof(uint32_t)) <= message_len;
       i += sizeof(uint32_t)) {
    uint32_t next_word = read_32(&message[i]);
    abs_mmio_write32(kBase + HMAC_MSG_FIFO_REG_OFFSET, next_word);
  }

  // For the last few bytes, we need to write one byte at a time again.
  for (; launder32(i) < message_len; i++) {
    abs_mmio_write8(kBase + HMAC_MSG_FIFO_REG_OFFSET, message[i]);
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
  uint32_t status = abs_mmio_read32(hmac_base() + HMAC_STATUS_REG_OFFSET);
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
 * @param msg Message buffer.
 * @param digest_wordlen Digest length in 32-bit words.
 * @param[out] digest Buffer for the digest.
 */
static status_t oneshot(const uint32_t cfg, const hmac_key_t *key,
                        const otcrypto_const_byte_buf_t *msg,
                        size_t digest_wordlen, uint32_t *digest) {
  // Check that the block is idle.
  HARDENED_TRY(ensure_idle());

  // Make sure that the entropy complex is configured correctly.
  HARDENED_TRY(entropy_complex_check());

  // Configure the HMAC block.
  abs_mmio_write32(hmac_base() + HMAC_CFG_REG_OFFSET, cfg);

  // Write the key (no-op if the key length is 0, e.g. for hashing).
  HARDENED_TRY(key_write(key));

  // Send the START command.
  uint32_t cmd =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_START_BIT, 1);
  abs_mmio_write32(hmac_base() + HMAC_CMD_REG_OFFSET, cmd);

  // Write the message.
  HARDENED_TRY(msg_fifo_write(msg->data, msg->len));

  // Send the PROCESS command.
  cmd = bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_PROCESS_BIT, 1);
  abs_mmio_write32(hmac_base() + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for the digest to be ready, then read it.
  HARDENED_TRY(hmac_idle_wait());
  digest_read(digest, digest_wordlen);

  // Read back the HMAC configuration and compare to the expected configuration.
  HARDENED_CHECK_EQ(abs_mmio_read32(hmac_base() + HMAC_CFG_REG_OFFSET),
                    launder32(cfg));

  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(msg));

  HARDENED_TRY(clear());
  return OTCRYPTO_OK;
}

status_t hmac_hash_sha256(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha256, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, msg, kHmacSha256DigestWords, digest);
}

status_t hmac_hash_sha384(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha384, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, msg, kHmacSha384DigestWords, digest);
}

status_t hmac_hash_sha512(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest) {
  uint32_t cfg =
      cfg_get(/*hmac_en=*/false, kDigestLengthSha512, kKeyLengthNone);
  return oneshot(cfg, /*key=*/NULL, msg, kHmacSha512DigestWords, digest);
}

status_t hmac_hmac_sha256(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha256, kKeyLength512);
  return oneshot(cfg, key, msg, tag->len, tag->data);
}

status_t hmac_hmac_sha256_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag) {
  uint32_t o_key_pad[kHmacSha256BlockWords];
  uint32_t i_key_pad[kHmacSha256BlockWords];
  memset(o_key_pad, 0, kHmacSha256BlockBytes);
  memset(i_key_pad, 0, kHmacSha256BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  uint32_t opad[kHmacSha256BlockWords];
  uint32_t ipad[kHmacSha256BlockWords];
  memset(opad, 0x5c5c5c5c, kHmacSha256BlockBytes);
  memset(ipad, 0x36363636, kHmacSha256BlockBytes);
  TRY(hardened_xor(key->key_block, opad, kHmacSha256BlockWords, o_key_pad));
  TRY(hardened_xor(key->key_block, ipad, kHmacSha256BlockWords, i_key_pad));

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg_data[kHmacSha256BlockBytes + msg->len];
  otcrypto_const_byte_buf_t i_key_pad_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, i_key_pad_msg_data,
                        sizeof(i_key_pad_msg_data));
  memset(i_key_pad_msg_data, 0, sizeof(i_key_pad_msg));
  randomized_bytecopy(i_key_pad_msg_data, i_key_pad, kHmacSha256BlockBytes);
  randomized_bytecopy(i_key_pad_msg_data + kHmacSha256BlockBytes, msg->data,
                      msg->len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha256DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha256(&i_key_pad_msg, h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash_data[kHmacSha256BlockBytes + kHmacSha256DigestBytes];
  otcrypto_const_byte_buf_t o_key_pad_hash =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, o_key_pad_hash_data,
                        sizeof(o_key_pad_hash_data));
  memset(o_key_pad_hash_data, 0, sizeof(o_key_pad_hash_data));
  randomized_bytecopy(o_key_pad_hash_data, o_key_pad, kHmacSha256BlockBytes);
  randomized_bytecopy(o_key_pad_hash_data + kHmacSha256BlockBytes,
                      o_key_pad_hash_data, kHmacSha256DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha256(&o_key_pad_hash, tag->data);
}

status_t hmac_hmac_sha384(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha384, kKeyLength1024);
  return oneshot(cfg, key, msg, tag->len, tag->data);
}

status_t hmac_hmac_sha384_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag) {
  uint32_t o_key_pad[kHmacSha384BlockWords];
  uint32_t i_key_pad[kHmacSha384BlockWords];
  memset(o_key_pad, 0, kHmacSha384BlockBytes);
  memset(i_key_pad, 0, kHmacSha384BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  for (size_t it = 0; it < kHmacSha384BlockWords; it++) {
    o_key_pad[it] = key->key_block[it] ^ 0x5c5c5c5c;
    i_key_pad[it] = key->key_block[it] ^ 0x36363636;
  }

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg_data[kHmacSha384BlockBytes + msg->len];
  otcrypto_const_byte_buf_t i_key_pad_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, i_key_pad_msg_data,
                        sizeof(i_key_pad_msg_data));
  memset(i_key_pad_msg_data, 0, sizeof(i_key_pad_msg_data));
  randomized_bytecopy(i_key_pad_msg_data, i_key_pad, kHmacSha384BlockBytes);
  randomized_bytecopy(i_key_pad_msg_data + kHmacSha384BlockBytes, msg->data,
                      msg->len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha384DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha384(&i_key_pad_msg, h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash_data[kHmacSha384BlockBytes + kHmacSha384DigestBytes];
  otcrypto_const_byte_buf_t o_key_pad_hash =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, o_key_pad_hash_data,
                        sizeof(o_key_pad_hash_data));
  memset(o_key_pad_hash_data, 0, sizeof(o_key_pad_hash_data));
  randomized_bytecopy(o_key_pad_hash_data, o_key_pad, kHmacSha384BlockBytes);
  randomized_bytecopy(o_key_pad_hash_data + kHmacSha384BlockBytes,
                      o_key_pad_hash_data, kHmacSha384DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha384(&o_key_pad_hash, tag->data);
}

status_t hmac_hmac_sha512(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag) {
  // Always configure the key length as the underlying message block size.
  uint32_t cfg = cfg_get(/*hmac_en=*/true, kDigestLengthSha512, kKeyLength1024);
  return oneshot(cfg, key, msg, tag->len, tag->data);
}

status_t hmac_hmac_sha512_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag) {
  uint32_t o_key_pad[kHmacSha512BlockWords];
  uint32_t i_key_pad[kHmacSha512BlockWords];
  memset(o_key_pad, 0, kHmacSha512BlockBytes);
  memset(i_key_pad, 0, kHmacSha512BlockBytes);

  // XOR the key K with the outer (opad) and inner (ipad) padding.
  for (size_t it = 0; it < kHmacSha512BlockWords; it++) {
    o_key_pad[it] = key->key_block[it] ^ 0x5c5c5c5c;
    i_key_pad[it] = key->key_block[it] ^ 0x36363636;
  }

  // Concatenate the message with the inner padded key.
  uint8_t i_key_pad_msg_data[kHmacSha512BlockBytes + msg->len];
  otcrypto_const_byte_buf_t i_key_pad_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, i_key_pad_msg_data,
                        sizeof(i_key_pad_msg_data));
  memset(i_key_pad_msg_data, 0, sizeof(i_key_pad_msg_data));
  randomized_bytecopy(i_key_pad_msg_data, i_key_pad, kHmacSha512BlockBytes);
  randomized_bytecopy(i_key_pad_msg_data + kHmacSha512BlockBytes, msg,
                      msg->len);

  // h_i_key_pad_msg = H(i_key_pad || m).
  uint32_t h_i_key_pad_msg[kHmacSha512DigestWords];
  memset(h_i_key_pad_msg, 0, sizeof(h_i_key_pad_msg));
  HARDENED_TRY(hmac_hash_sha512(&i_key_pad_msg, h_i_key_pad_msg));

  // Concatenate the outer padded key with h_i_key_pad_msg.
  uint8_t o_key_pad_hash_data[kHmacSha512BlockBytes + kHmacSha512DigestBytes];
  otcrypto_const_byte_buf_t o_key_pad_hash =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, o_key_pad_hash_data,
                        sizeof(o_key_pad_hash_data));
  memset(o_key_pad_hash_data, 0, sizeof(o_key_pad_hash_data));
  randomized_bytecopy(o_key_pad_hash_data, o_key_pad, kHmacSha512BlockBytes);
  randomized_bytecopy(o_key_pad_hash_data + kHmacSha512BlockBytes,
                      h_i_key_pad_msg, kHmacSha512DigestBytes);

  // hmac = H(o_key_pad || h_i_key_pad_msg).
  return hmac_hash_sha512(&o_key_pad_hash, tag->data);
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
  ctx->key.key_len = 0;
  ctx->key.checksum = 0;
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

void hmac_hmac_sha256_init(const hmac_key_t key, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha256BlockWords,
  ctx->digest_wordlen = kHmacSha256DigestWords;
  ctx->key.key_len = key.key_len;
  ctx->key.checksum = key.checksum;
  hardened_memcpy(ctx->key.key_block, key.key_block, key.key_len);
  HARDENED_CHECK_EQ(
      hardened_memeq(key.key_block, ctx->key.key_block, key.key_len),
      kHardenedBoolTrue);
  hmac_init(kKeyLength512, kDigestLengthSha256, ctx);
}

void hmac_hmac_sha384_init(const hmac_key_t key, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha384BlockWords,
  ctx->digest_wordlen = kHmacSha384DigestWords;
  ctx->key.key_len = key.key_len;
  ctx->key.checksum = key.checksum;
  hardened_memcpy(ctx->key.key_block, key.key_block, key.key_len);
  HARDENED_CHECK_EQ(
      hardened_memeq(key.key_block, ctx->key.key_block, key.key_len),
      kHardenedBoolTrue);
  hmac_init(kKeyLength1024, kDigestLengthSha384, ctx);
}

void hmac_hmac_sha512_init(const hmac_key_t key, hmac_ctx_t *ctx) {
  ctx->msg_block_wordlen = kHmacSha512BlockWords,
  ctx->digest_wordlen = kHmacSha512DigestWords;
  ctx->key.key_len = key.key_len;
  ctx->key.checksum = key.checksum;
  hardened_memcpy(ctx->key.key_block, key.key_block, key.key_len);
  HARDENED_CHECK_EQ(
      hardened_memeq(key.key_block, ctx->key.key_block, key.key_len),
      kHardenedBoolTrue);
  hmac_init(kKeyLength1024, kDigestLengthSha512, ctx);
}

uint32_t hmac_key_integrity_checksum(const hmac_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->key_len);
  crc32_add(&ctx, (unsigned char *)key->key_block, key->key_len);
  return crc32_finish(&ctx);
}

hardened_bool_t hmac_key_integrity_checksum_check(const hmac_key_t *key) {
  if (key->checksum == launder32(hmac_key_integrity_checksum(key))) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

status_t hmac_update(hmac_ctx_t *ctx, const otcrypto_const_byte_buf_t *data) {
  // Make sure that the entropy complex is configured correctly.
  HARDENED_TRY(entropy_complex_check());

  // If we don't have enough new bytes to fill a block, just update the partial
  // block and return.
  size_t block_bytelen = ctx->msg_block_wordlen * sizeof(uint32_t);
  if (data->len < block_bytelen - ctx->partial_block_bytelen) {
    memcpy((unsigned char *)(ctx->partial_block) + ctx->partial_block_bytelen,
           data->data, data->len);
    ctx->partial_block_bytelen += data->len;
    return OTCRYPTO_OK;
  }

  // Calculate the number of bytes that will be in the next partial block.
  // Reduce `len` modulo the block length preemptively to protect against
  // integer overflow when adding to the partial length.
  size_t len_rem = data->len % block_bytelen;
  size_t leftover_len = (ctx->partial_block_bytelen + len_rem) % block_bytelen;

  // Retore context will restore the context and also hit start or continue
  // button as necessary.
  HARDENED_TRY(context_restore(ctx));

  // Write the partial block, then the new bytes.
  HARDENED_TRY(msg_fifo_write((unsigned char *)ctx->partial_block,
                              ctx->partial_block_bytelen));
  HARDENED_TRY(msg_fifo_write(data->data, data->len - leftover_len));

  // Send the STOP command.
  uint32_t cmd =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_STOP_BIT, 1);
  abs_mmio_write32(hmac_base() + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for HMAC to be done, then store the context.
  HARDENED_TRY(hmac_idle_wait());
  context_save(ctx);

  // Write leftover bytes to `partial_block`, so that future update/final call
  // can feed them to HMAC HWIP.
  memcpy(ctx->partial_block, data->data + (data->len - leftover_len),
         leftover_len);
  ctx->partial_block_bytelen = leftover_len;

  // Clean up.
  HARDENED_TRY(clear());

  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(data));

  return OTCRYPTO_OK;
}

status_t hmac_final(hmac_ctx_t *ctx, otcrypto_word32_buf_t *digest) {
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
  abs_mmio_write32(hmac_base() + HMAC_CMD_REG_OFFSET, cmd);

  // Wait for HMAC to be done, then read the digest.
  HARDENED_TRY(hmac_idle_wait());
  digest_read(digest->data, ctx->digest_wordlen);

  // Destroy sensitive values in the ctx object.
  HARDENED_TRY(hmac_context_wipe(ctx));

  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(digest));

  // Clean up.
  HARDENED_TRY(clear());
  return OTCRYPTO_OK;
}
