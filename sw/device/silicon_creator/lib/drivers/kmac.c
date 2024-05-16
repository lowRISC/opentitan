// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

enum {
  /**
   * Base address of the KMAC hardware MMIO interface.
   */
  kBase = TOP_EARLGREY_KMAC_BASE_ADDR,
  /**
   * Keccak capacity for SHAKE256.
   *
   * See FIPS 202, section 6.2.
   */
  kShake256KeccakCapacity = 2 * 256,
  /**
   * Keccak rate for SHAKE256 (bits).
   *
   * Rate is 1600 - capacity (FIPS 202, section 6.2).
   */
  kShake256KeccakRateBits = 1600 - kShake256KeccakCapacity,
  /**
   * Keccak rate for SHAKE256 (bytes).
   */
  kShake256KeccakRateBytes = kShake256KeccakRateBits / 8,
  /**
   * Keccak rate for SHAKE256 (words).
   */
  kShake256KeccakRateWords = kShake256KeccakRateBytes / sizeof(uint32_t),
  /**
   * Size of one share of the Keccak state.
   */
  kStateShareSize = KMAC_STATE_SIZE_BYTES / 2,
  /**
   * Address of first share of Keccak state.
   */
  kAddrStateShare0 = kBase + KMAC_STATE_REG_OFFSET,
  /**
   * Address of second share of Keccak state.
   */
  kAddrStateShare1 = kBase + KMAC_STATE_REG_OFFSET + kStateShareSize,
};

// Double-check that calculated rate is smaller than one share of the state.
static_assert(kShake256KeccakRateWords <= kStateShareSize,
              "assert SHAKE256 rate is <= share size");

static const uint32_t kEntropySeed[] = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a,
                                        0x48465647, 0x70410fef};

/**
 * KMAC configuration parameters.
 */
typedef struct kmac_config {
  /**
   * Entropy fast process mode when enabled prevents the KMAC unit consuming
   * entropy unless it is processing a secret key. This process should not be
   * used when resistance against side-channel attacks is required, because
   * it may lead to leakage of the secret key in the power trace.
   */
  bool entropy_fast_process;
  /**
   * Message Masking with PRNG.
   * If true, KMAC applies PRNG to the input messages to the Keccak module when
   * KMAC mode is on.
   */
  bool msg_mask;
  /**
   * Enable KMAC sideload mode.
   */
  bool sideload;
  /**
   * Whether or not to use enable KMAC mode.
   */
  bool kmac_en;

  /**
   * The algorithm: SHA3, SHAKE or cSHAKE
   */
  uint8_t mode;
} kmac_config_t;

/**
 * Polls the KMAC block state until the desired status bit is set.
 *
 * If the KMAC block registers an error, this routine exits early and returns
 * `kErrorKmacInvalidStatus`.
 *
 * @param bit_index Bit within the status register to poll.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t poll_state(bitfield_bit32_index_t bit_index) {
  // The success condition of this function is:
  //   - The specified bit in the status register is 1, and
  //   - The error bit in KMAC's INTR_STATE register is 0.
  //
  // In order to make fault injection more difficult, we compute these values
  // in a slightly convoluted way so that skipping any few instructions will
  // not reach the success condition.
  uint32_t status = 0;
  rom_error_t res = launder32(kErrorOk ^ UINT32_MAX);
  uint32_t is_error = (uint32_t)kHardenedBoolFalse;
  do {
    // Read the error bit.
    uint32_t intr_state = abs_mmio_read32(kBase + KMAC_INTR_STATE_REG_OFFSET);
    uint32_t err_bit = launder32((uint32_t)bitfield_bit32_read(
        intr_state, KMAC_INTR_STATE_KMAC_ERR_BIT));
    // If there is no error, (~err_bit) + 1 will be zero and `is_error` will
    // remain `kHardenedBoolFalse`. Otherwise, ~err_bit + 1 will be
    // UINT32_MAX and all bits will flip to produce a garbage value.
    is_error ^= (~err_bit) + 1;

    // Read the status register.
    status = abs_mmio_read32(kBase + KMAC_STATUS_REG_OFFSET);
    uint32_t flag = launder32((uint32_t)bitfield_bit32_read(status, bit_index));
    // If `flag` is 0, then `res` will be unchanged (and remain `kErrorOk ^
    // UINT32_MAX`).  If it is 1, then all bits except the LSB will flip,
    // meaning `res = kErrorOk ^ 1`.
    res ^= ((~flag) + 1) << 1;
  } while (!bitfield_bit32_read(launder32(status), bit_index) &&
           launder32(is_error) == kHardenedBoolFalse);

  // If the bit is set, this xor will set `res = kErrorOk`.
  res ^= bitfield_bit32_read(status, bit_index);

  if (launder32(is_error) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(is_error, kHardenedBoolFalse);
    // The only way to get here is if the desired flag is set, meaning `res =
    // kErrorOk`.
    return res;
  }

  return kErrorKmacInvalidStatus;
}

/**
 * Configure kmac block using `config` parameters.
 *
 * @param config The kmac configuration parameters.
 *
 * @return Error code indicating if the operation succeeded.
 */
static rom_error_t kmac_configure(kmac_config_t config) {
  HARDENED_RETURN_IF_ERROR(poll_state(KMAC_STATUS_SHA3_IDLE_BIT));

  uint32_t entropy_period_reg = KMAC_ENTROPY_PERIOD_REG_RESVAL;
  // Set the wait timer to the maximum count.
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD,
      KMAC_ENTROPY_PERIOD_WAIT_TIMER_MASK);
  // Set the prescaler to the maximum number of cycles.
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_PRESCALER_FIELD,
      KMAC_ENTROPY_PERIOD_PRESCALER_MASK);
  abs_mmio_write32(kBase + KMAC_ENTROPY_PERIOD_REG_OFFSET, entropy_period_reg);

  uint32_t cfg_reg = KMAC_CFG_SHADOWED_REG_RESVAL;
  // Set `CFG.KMAC_EN` bit to 0.
  // NOTE: If this driver is ever modified to perform an operation with
  // KMAC_EN=true and use entropy from EDN, then the absorb() function must
  // poll `STATUS.fifo_depth` to avoid a specific EDN-KMAC-Ibex deadlock
  // scenario. See `absorb()` and the KMAC documentation for details.
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, 0);
  // Set `CFG.KSTRENGTH` field to 256-bit strength.
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
  // Set `CFG.MODE` field to SHAKE.
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   config.mode);
  // Set `CFG.MSG_ENDIANNESS` bit to 0 (little-endian).
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT, 0);
  // Set `CFG.STATE_ENDIANNESS` bit to 0 (little-endian).
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, 0);

  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT,
                                 config.sideload);

  // Set `CFG.ENTROPY_MODE` field to use software entropy. SHAKE does not
  // require any entropy, so there is no reason we should wait for entropy
  // availability before we start hashing.
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_MODE_FIELD,
                             KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_SW_MODE);

  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT,
                           config.entropy_fast_process);

  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_MASK_BIT,
                                 config.msg_mask);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT,
                                 config.kmac_en);

  // Set `CFG.ENTROPY_READY` bit to 1.
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, 1);
  // Set `CFG.ERR_PROCESSED` bit to 0.
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ERR_PROCESSED_BIT, 0);
  // Set `CFG.EN_UNSUPPORTED_MODESTRENGTH` bit to 0.
  cfg_reg = bitfield_bit32_write(
      cfg_reg, KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT, 0);
  abs_mmio_write32_shadowed(kBase + KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Write entropy seed registers. Even though the values are
  // irrelevant, these registers must be written for the KMAC block to consider
  // its entropy "ready" and to begin operation.
  abs_mmio_write32(kBase + KMAC_ENTROPY_SEED_0_REG_OFFSET, kEntropySeed[0]);
  abs_mmio_write32(kBase + KMAC_ENTROPY_SEED_1_REG_OFFSET, kEntropySeed[1]);
  abs_mmio_write32(kBase + KMAC_ENTROPY_SEED_2_REG_OFFSET, kEntropySeed[2]);
  abs_mmio_write32(kBase + KMAC_ENTROPY_SEED_3_REG_OFFSET, kEntropySeed[3]);
  abs_mmio_write32(kBase + KMAC_ENTROPY_SEED_4_REG_OFFSET, kEntropySeed[4]);

  return kErrorOk;
}

/**
 * Issue a command to the KMAC block.
 *
 * @param cmd_value Value to write to the CMD register.
 */
static void issue_command(uint32_t cmd_value) {
  uint32_t cmd_reg = bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, cmd_value);
  abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);
}

rom_error_t kmac_keymgr_configure(void) {
  return kmac_configure((kmac_config_t){
      .entropy_fast_process = false,
      .msg_mask = true,
      .sideload = true,
      .kmac_en = false,
      .mode = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE,
  });
}

rom_error_t kmac_kmac256_sw_configure(void) {
  kmac_kmac256_set_prefix(NULL, 0);
  return kmac_configure((kmac_config_t){
      .entropy_fast_process = false,
      .msg_mask = false,
      .sideload = false,
      .kmac_en = true,
      .mode = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE,
  });
}

rom_error_t kmac_kmac256_hw_configure(void) {
  kmac_kmac256_set_prefix(NULL, 0);
  return kmac_configure((kmac_config_t){
      .entropy_fast_process = false,
      .msg_mask = false,
      .sideload = true,
      .kmac_en = true,
      .mode = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE,
  });
}

rom_error_t kmac_shake256_configure(void) {
  return kmac_configure((kmac_config_t){
      .entropy_fast_process = false,
      .msg_mask = false,
      .sideload = false,
      .kmac_en = false,
      .mode = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE,
  });
}

rom_error_t kmac_shake256_start(void) {
  // Block until KMAC hardware is idle.
  HARDENED_RETURN_IF_ERROR(poll_state(KMAC_STATUS_SHA3_IDLE_BIT));

  // Issue `CMD.START` to start the operation.
  issue_command(KMAC_CMD_CMD_VALUE_START);

  // Block until KMAC hardware is in the `absorb` state. After `CMD.START`,
  // KMAC should never move out of the `absorb` state until `CMD.PROCESS` is
  // issued, so we get significant performance gains by polling only once here
  // instead of before every `absorb`.
  HARDENED_RETURN_IF_ERROR(poll_state(KMAC_STATUS_SHA3_ABSORB_BIT));

  return kErrorOk;
}

void kmac_shake256_absorb(const uint8_t *in, size_t inlen) {
  // This implementation does not poll `STATUS.fifo_depth` as recommended in
  // the KMAC documentation. Normally, polling is required to prevent a
  // deadlock scenario between Ibex, KMAC, and EDN. However, in this case it is
  // safe to skip because `kmac_shake256_configure()` sets KMAC to use
  // software-only entropy, and sets `kmac_en` to false (so KMAC will not
  // produce entropy requests anyway). Since KMAC will therefore not block on
  // EDN, it is guaranteed to keep processing message blocks. For more details,
  // see the KMAC documentation:
  //   https://docs.opentitan.org/hw/ip/kmac/doc/#fifo-depth-and-empty-status

  // Use byte-wide writes until the input pointer is aligned.
  // Note: writes to the KMAC message FIFO are not required to be aligned.
  for (; inlen > 0 && misalignment32_of((uintptr_t)in); --inlen, ++in) {
    abs_mmio_write8(kBase + KMAC_MSG_FIFO_REG_OFFSET, *in);
  }

  // Use word writes for all full words.
  for (; inlen >= sizeof(uint32_t);
       inlen -= sizeof(uint32_t), in += sizeof(uint32_t)) {
    abs_mmio_write32(kBase + KMAC_MSG_FIFO_REG_OFFSET, read_32(in));
  }

  // Use byte-wide writes for anything left over.
  for (; inlen > 0; --inlen, ++in) {
    abs_mmio_write8(kBase + KMAC_MSG_FIFO_REG_OFFSET, *in);
  }
  HARDENED_CHECK_EQ(inlen, 0);
}

void kmac_shake256_absorb_words(const uint32_t *in, size_t inlen) {
  // This implementation does not poll `STATUS.fifo_depth` as recommended in
  // the KMAC documentation. Normally, polling is required to prevent a
  // deadlock scenario between Ibex, KMAC, and EDN. However, in this case it is
  // safe to skip because `kmac_shake256_configure()` sets KMAC to use
  // software-only entropy, and sets `kmac_en` to false (so KMAC will not
  // produce entropy requests anyway). Since KMAC will therefore not block on
  // EDN, it is guaranteed to keep processing message blocks. For more details,
  // see the KMAC documentation:
  //   https://docs.opentitan.org/hw/ip/kmac/doc/#fifo-depth-and-empty-status

  for (; inlen > 0; --inlen, ++in) {
    abs_mmio_write32(kBase + KMAC_MSG_FIFO_REG_OFFSET, *in);
  }
  HARDENED_CHECK_EQ(inlen, 0);
}

void kmac_shake256_squeeze_start(void) {
  // Issue `CMD.PROCESS` to move to the squeezing state.
  issue_command(KMAC_CMD_CMD_VALUE_PROCESS);
}

rom_error_t kmac_shake256_squeeze_end(uint32_t *out, size_t outlen) {
  size_t idx = 0;
  while (launder32(idx) < outlen) {
    // Since we always read in increments of the SHAKE-256 rate, the index at
    // start should always be a multiple of the rate.
    HARDENED_CHECK_EQ(idx % kShake256KeccakRateWords, 0);

    // Poll the status register until in the 'squeeze' state.
    HARDENED_RETURN_IF_ERROR(poll_state(KMAC_STATUS_SHA3_SQUEEZE_BIT));

    // Read words from the state registers (either `outlen` or the maximum
    // number of words available).
    size_t offset = 0;
    for (; launder32(idx) < outlen && offset < kShake256KeccakRateWords;
         ++offset) {
      uint32_t share0 =
          abs_mmio_read32(kAddrStateShare0 + offset * sizeof(uint32_t));
      uint32_t share1 =
          abs_mmio_read32(kAddrStateShare1 + offset * sizeof(uint32_t));
      out[idx] = share0 ^ share1;
      ++idx;
    }

    if (offset == kShake256KeccakRateWords) {
      // If we read all the remaining words, issue `CMD.RUN` to generate more
      // state.
      HARDENED_CHECK_EQ(offset, kShake256KeccakRateWords);
      issue_command(KMAC_CMD_CMD_VALUE_RUN);
    }
  }
  HARDENED_CHECK_EQ(idx, outlen);

  // Poll the status register until in the 'squeeze' state.
  HARDENED_RETURN_IF_ERROR(poll_state(KMAC_STATUS_SHA3_SQUEEZE_BIT));

  // Issue `CMD.DONE` to finish the operation.
  issue_command(KMAC_CMD_CMD_VALUE_DONE);

  return kErrorOk;
}

#define WORD_BITS (sizeof(uint32_t) * 8)
#define KEY_CASE(x_)                       \
  case x_ / WORD_BITS:                     \
    klen = KMAC_KEY_LEN_LEN_VALUE_KEY##x_; \
    break
rom_error_t kmac_kmac256_sw_key(const uint32_t *key, size_t len) {
  uint32_t klen;
  switch (len) {
    KEY_CASE(128);
    KEY_CASE(192);
    KEY_CASE(256);
    KEY_CASE(384);
    KEY_CASE(512);
    default:
      return kErrorKmacInvalidKeySize;
  }
  abs_mmio_write32(kBase + KMAC_KEY_LEN_REG_OFFSET, klen);
  for (size_t i = 0; i < KMAC_KEY_SHARE0_MULTIREG_COUNT; ++i) {
    uint32_t value = i < len ? key[i] : 0;
    abs_mmio_write32(
        kBase + KMAC_KEY_SHARE0_0_REG_OFFSET + i * sizeof(uint32_t), value);
    abs_mmio_write32(
        kBase + KMAC_KEY_SHARE1_0_REG_OFFSET + i * sizeof(uint32_t), 0);
  }
  return kErrorOk;
}

void kmac_kmac256_set_prefix(const void *prefix, size_t len) {
  // The length must be less than 32 because this function encodes the prefix
  // length as a single byte, and 32*8 == 256, which won't fit in a byte.
  HARDENED_CHECK_LT(len, 32);
  uint32_t regs[KMAC_PREFIX_MULTIREG_COUNT] = {
      0x4D4B2001,  //  1  32  'K' 'M'
      0x00014341,  // 'A' 'C'  1   0
  };
  char *r = (char *)&regs[2];

  // The prefix length is the byte immediately before where we'll store the
  // message (the last `0` byte in the `regs` above).  Set the length and
  // then copy the prefix into the `regs` buffer.
  r[-1] = (char)(len * 8);
  memcpy(r, prefix, len);

  for (size_t i = 0; i < KMAC_PREFIX_MULTIREG_COUNT; ++i) {
    abs_mmio_write32(kBase + KMAC_PREFIX_0_REG_OFFSET + i * sizeof(uint32_t),
                     regs[i]);
  }
}

rom_error_t kmac_kmac256_final(uint32_t *result, size_t rlen) {
  // To finalize a kmac operation, we need to right-pad the bit-length of the
  // result buffer and absorb that padded length value into the sponge.
  uint8_t buffer[sizeof(size_t) + 1];
  size_t val = rlen * 32;
  size_t n = 0;
  size_t p = sizeof(buffer) - 1;
  while (val) {
    buffer[--p] = val & 0xFF;
    val >>= 8;
    n++;
  }
  buffer[sizeof(buffer) - 1] = (uint8_t)n;
  kmac_shake256_absorb(buffer + p, n + 1);

  // Now, squeeze out the result.
  kmac_shake256_squeeze_start();
  return kmac_shake256_squeeze_end(result, rlen);
}

// Provide link locations for the inline functions in the header file.
extern rom_error_t kmac_kmac256_start(void);
extern void kmac_kmac256_absorb(const void *data, size_t len);
