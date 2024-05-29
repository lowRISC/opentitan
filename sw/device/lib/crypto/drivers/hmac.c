// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
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

/**
 * The following values are the only key sizes supported natively bw HWIP.
 */
enum {
  /* The beginning of the address space of HMAC. */
  kHmacBaseAddr = TOP_EARLGREY_HMAC_BASE_ADDR,
  /* Internal block size for SHA-256/HMAC-256 in bits. */
  kHmacSha256InternalBlockBits = 512,
  kHmacSha256InternalBlockBytes = kHmacSha256InternalBlockBits / 8,
  /* Internal block size for SHA-384/HMAC-384 in bits. */
  kHmacSha384InternalBlockBits = 1024,
  kHmacSha384InternalBlockBytes = kHmacSha384InternalBlockBits / 8,
  /* Internal block size for SHA-512/HMAC-512 in bits. */
  kHmacSha512InternalBlockBits = 1024,
  kHmacSha512InternalBlockBytes = kHmacSha512InternalBlockBits / 8,
};

/**
 * Wait until HMAC raises `hmac_done` interrupt. After interrupt is observed,
 * clear it.
 *
 * TODO(#23191): Avoid constant loop and use to-be-implemented Idle/status bit
 * instead.
 */
static void hmac_done_wait(void) {
  uint32_t intr_reg = 0;
  while (bitfield_bit32_read(intr_reg, HMAC_INTR_STATE_HMAC_DONE_BIT) == 0) {
    intr_reg = abs_mmio_read32(kHmacBaseAddr + HMAC_INTR_STATE_REG_OFFSET);
  }

  // Clear the interrupt by writing 1, because `INTR_STATE` is rw1c type.
  abs_mmio_write32(kHmacBaseAddr + HMAC_INTR_STATE_REG_OFFSET, intr_reg);
}

/**
 * Clear the state of HMAC HWIP so that further driver calls can use it.
 *
 * This function cannot force stop HWIP, and ongoing operations will not simply
 * stop by deasserting `sha_en` bit. Instead it should be used after HWIP
 * raises `hmac_done` interrupt (see `hmac_done_wait` function).
 *
 * It also clears the internal state of HWIP by overwriting sensitive values
 * with 1s.
 */
static void hmac_hwip_clear(void) {
  // Do not clear the config yet, we just need to deassert sha_en, see #23014.
  // TODO handle digest size changes.
  uint32_t cfg_reg = abs_mmio_read32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg_reg);

  // TODO(#23191): Use a random value from EDN to wipe.
  abs_mmio_write32(kHmacBaseAddr + HMAC_WIPE_SECRET_REG_OFFSET, UINT32_MAX);
}

/**
 * Restore the internal state of HWIP from `ctx` struct, and resume the
 * operation.
 *
 * The first HWIP operation requires the call of `start` instead of `continue`.
 * Therefore, `ctx->hw_started` flag is used to distinguish the first call. This
 * function also updated `ctx->hw_started` after the first such call.
 *
 * If this function is being called from `ctx` object with previously stored
 * context (i.e. `ctx->hw_started = true`), then this state is restored.
 *
 * @param ctx Context from which values are written to CSRs.
 */
static void context_restore(hmac_ctx_t *ctx) {
  // Restore CFG register from `ctx->cfg_reg`.
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, ctx->cfg_reg);

  // Write to KEY registers for HMAC operations. If the operation is SHA-2,
  // `key_len` is set to 0 during `ctx` initialization.
  for (size_t i = 0; i < ctx->key_len; i++) {
    abs_mmio_write32(kHmacBaseAddr + HMAC_KEY_0_REG_OFFSET + 4 * i,
                     ctx->key[i]);
  }

  uint32_t cmd_reg = HMAC_CMD_REG_RESVAL;
  // Decide if we need to invoke `start` or `continue` command.
  if (ctx->hw_started) {
    cmd_reg = bitfield_bit32_write(cmd_reg, HMAC_CMD_HASH_CONTINUE_BIT, 1);

    // For SHA-256 and HMAC-256, we do not need to write to the second half of
    // DIGEST registers, but we do it anyway to keep the driver simple.
    for (size_t i = 0; i < kHmacMaxDigestWords; i++) {
      abs_mmio_write32(kHmacBaseAddr + HMAC_DIGEST_0_REG_OFFSET + 4 * i,
                       ctx->H[i]);
    }
    abs_mmio_write32(kHmacBaseAddr + HMAC_MSG_LENGTH_LOWER_REG_OFFSET,
                     ctx->lower);
    abs_mmio_write32(kHmacBaseAddr + HMAC_MSG_LENGTH_UPPER_REG_OFFSET,
                     ctx->upper);
  } else {
    cmd_reg = bitfield_bit32_write(cmd_reg, HMAC_CMD_HASH_START_BIT, 1);
    ctx->hw_started = 1;
  }

  // We could not set `sha_en` before updating context registers (see #23014).
  // Now that context registers are restored, enable `sha_en`.
  uint32_t cfg_reg = abs_mmio_read32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, HMAC_CFG_SHA_EN_BIT, true);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CFG_REG_OFFSET, cfg_reg);

  // Now we can finally write the command to the register to actually issue
  // `start` or `continue`.
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd_reg);
}

/**
 * Save the context from HWIP into `ctx` object.
 *
 * This function should be called only after `stop` command is invoked and HWIP
 * confirms that it stopped via interrupt.
 *
 * @param[out] ctx Context to which values are written.
 */
static void context_save(hmac_ctx_t *ctx) {
  // For SHA-256 and HMAC-256, we do not need to save to the second half of
  // DIGEST registers, but we do it anyway to keep the driver simple.
  for (size_t i = 0; i < kHmacMaxDigestWords; i++) {
    ctx->H[i] =
        abs_mmio_read32(kHmacBaseAddr + HMAC_DIGEST_0_REG_OFFSET + 4 * i);
  }
  ctx->lower =
      abs_mmio_read32(kHmacBaseAddr + HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  ctx->upper =
      abs_mmio_read32(kHmacBaseAddr + HMAC_MSG_LENGTH_UPPER_REG_OFFSET);
}

/**
 * Write given byte array into the `MSG_FIFO`. This function should only be
 * called when HWIP is already running and expecting further message bytes.
 */
static void msg_fifo_write(const uint8_t *msg, size_t msg_len) {
  // TODO(#23191): Improve message copying by writing them in 32b at a time.
  for (size_t i = 0; i < msg_len; i++) {
    abs_mmio_write8(kHmacBaseAddr + HMAC_MSG_FIFO_REG_OFFSET, msg[i]);
  }
}

status_t hmac_init(hmac_ctx_t *ctx, const hmac_mode_t hmac_mode,
                   const hmac_key_t *key) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  // TODO(#23191) Zeroise or randomly populate ctx struct during init.

  // Prepare cfg_reg in context.
  ctx->cfg_reg = HMAC_CFG_REG_RESVAL;
  // The endianness is fixed at driver level and not exposed to the caller.
  // Digest should be big-endian to match the SHA-256 specification.
  ctx->cfg_reg =
      bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_DIGEST_SWAP_BIT, true);
  // Message should be little-endian to match Ibex's endianness.
  ctx->cfg_reg =
      bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);

  // We need to keep `sha_en` low until context is restored, see #23014.
  ctx->cfg_reg = bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_SHA_EN_BIT, false);

  // Default value for `hmac_en` is false, HMAC calls set it to true below.
  ctx->cfg_reg =
      bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_HMAC_EN_BIT, false);

  switch (hmac_mode) {
    case kHmacModeHmac256:
      ctx->cfg_reg =
          bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_HMAC_EN_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kHmacModeSha256:
      ctx->cfg_reg =
          bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                                 HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256);
      // The unit for `ctx->msg_block_len` is bytes.
      ctx->msg_block_len = kHmacSha256InternalBlockBytes;
      // The unit for `ctx->digest_len` is bytes.
      ctx->digest_len = kHmacSha256DigestBytes;
      break;
    case kHmacModeHmac384:
      ctx->cfg_reg =
          bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_HMAC_EN_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kHmacModeSha384:
      ctx->cfg_reg =
          bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                                 HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_384);
      // The unit for `ctx->msg_block_len` is bytes.
      ctx->msg_block_len = kHmacSha384InternalBlockBytes;
      // The unit for `ctx->digest_len` is bytes.
      ctx->digest_len = kHmacSha384DigestBytes;
      break;
    case kHmacModeHmac512:
      ctx->cfg_reg =
          bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_HMAC_EN_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kHmacModeSha512:
      ctx->cfg_reg =
          bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                                 HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512);
      // The unit for `ctx->msg_block_len` is bytes.
      ctx->msg_block_len = kHmacSha512InternalBlockBytes;
      // The unit for `ctx->digest_len` is bytes.
      ctx->digest_len = kHmacSha512DigestBytes;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  if (hmac_mode == kHmacModeHmac256 || hmac_mode == kHmacModeHmac384 ||
      hmac_mode == kHmacModeHmac512) {
    if (key == NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    ctx->cfg_reg =
        bitfield_bit32_write(ctx->cfg_reg, HMAC_CFG_HMAC_EN_BIT, true);
    // Key values supported natively by HW are {128, 256, 384, 512, 1024}.
    switch (key->len) {
      case kHmacKey128Bytes:
        ctx->cfg_reg =
            bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_KEY_LENGTH_FIELD,
                                   HMAC_CFG_KEY_LENGTH_VALUE_KEY_128);
        break;
      case kHmacKey256Bytes:
        ctx->cfg_reg =
            bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_KEY_LENGTH_FIELD,
                                   HMAC_CFG_KEY_LENGTH_VALUE_KEY_256);
        break;
      case kHmacKey384Bytes:
        ctx->cfg_reg =
            bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_KEY_LENGTH_FIELD,
                                   HMAC_CFG_KEY_LENGTH_VALUE_KEY_384);
        break;
      case kHmacKey512Bytes:
        ctx->cfg_reg =
            bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_KEY_LENGTH_FIELD,
                                   HMAC_CFG_KEY_LENGTH_VALUE_KEY_512);
        break;
      case kHmacKey1024Bytes:
        ctx->cfg_reg =
            bitfield_field32_write(ctx->cfg_reg, HMAC_CFG_KEY_LENGTH_FIELD,
                                   HMAC_CFG_KEY_LENGTH_VALUE_KEY_1024);
        break;
      default:
        return OTCRYPTO_BAD_ARGS;
    }
    // `ctx->key_len` has 32b as unit.
    ctx->key_len = key->len / sizeof(uint32_t);
    for (size_t i = 0; i < ctx->key_len; i++) {
      // TODO(#23158): Use `key_swap` to avoid endianness change.
      ctx->key[i] = (0xff & key->key[0]) << 24 | (0xff00 & key->key[1]) << 8 |
                    (0xff0000 & key->key[2]) >> 8 |
                    (0xff000000 & key->key[3]) >> 24;
    }
  } else {
    // Ensure that `key` is NULL for hashing operations.
    if (key != NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Set `key_len` to 0, so that it is clear this is hash operation. This
    // value is later used to skip writing to KEY registers.
    ctx->key_len = 0;
  }

  ctx->hw_started = 0;
  ctx->partial_block_len = 0;

  return OTCRYPTO_OK;
}

status_t hmac_update(hmac_ctx_t *ctx, const uint8_t *data, size_t len) {
  if (ctx == NULL || (data == NULL && len > 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check if incoming message bits with `ctx->partial_block` together has
  // enough bits to fill an internal SHA-2 block. Otherwise, this function just
  // appends the incoming bits to partial_block and returns without invoking
  // HWIP operation.
  if (ctx->partial_block_len + len < ctx->msg_block_len) {
    memcpy(ctx->partial_block + ctx->partial_block_len, data, len);
    ctx->partial_block_len += len;
    return OTCRYPTO_OK;
  }

  // `leftover` bits refers to the size of the next partial block, after we
  // handle the current partial block and the incoming message bytes.
  size_t leftover_len = (ctx->partial_block_len + len) % ctx->msg_block_len;

  // The previous caller should have left it clean, but it doesn't hurt to
  // clear again.
  hmac_hwip_clear();
  // Retore context will restore the context and also hit start or continue
  // button as necessary.
  context_restore(ctx);

  // Write `partial_block` to MSG_FIFO
  msg_fifo_write(ctx->partial_block, ctx->partial_block_len);

  // Keep writing incoming bytes
  // TODO(#23191): Should we handle backpressure here?
  msg_fifo_write(data, len - leftover_len);

  // Time to tell HWIP to stop, because we do not have enough message bytes for
  // another round.
  uint32_t cmd_reg =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_STOP_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd_reg);

  // Wait for HWIP to be done.
  hmac_done_wait();

  // Store context into `ctx`.
  context_save(ctx);

  // Write leftover bytes to `partial_block`, so that future update/final call
  // can feed them to HWIP.
  memcpy(ctx->partial_block, data + len - leftover_len, leftover_len);
  ctx->partial_block_len = leftover_len;

  // Clean up HWIP so it can be reused by other driver calls.
  hmac_hwip_clear();
  return OTCRYPTO_OK;
}

status_t hmac_final(hmac_ctx_t *ctx, hmac_digest_t *digest) {
  if (ctx == NULL || digest == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that `digest_len` match the one from ctx.
  if (ctx->digest_len != digest->len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // The previous caller should have left it clean, but it doesn't hurt to
  // clear again.
  hmac_hwip_clear();

  // Retore context will restore the context and also hit start or continue
  // button as necessary.
  context_restore(ctx);

  // Feed the final leftover bytes to HWIP.
  msg_fifo_write(ctx->partial_block, ctx->partial_block_len);

  // All message bytes are fed, now hit the process button.
  uint32_t cmd_reg =
      bitfield_bit32_write(HMAC_CMD_REG_RESVAL, HMAC_CMD_HASH_PROCESS_BIT, 1);
  abs_mmio_write32(kHmacBaseAddr + HMAC_CMD_REG_OFFSET, cmd_reg);
  hmac_done_wait();

  for (size_t i = 0; i < ctx->digest_len / sizeof(uint32_t); i++) {
    digest->digest[i] =
        abs_mmio_read32(kHmacBaseAddr + HMAC_DIGEST_0_REG_OFFSET + 4 * i);
  }

  // Clean up HWIP so it can be reused by other driver calls.
  hmac_hwip_clear();

  // TODO(#23191): Destroy sensitive values in the ctx object.
  return OTCRYPTO_OK;
}
