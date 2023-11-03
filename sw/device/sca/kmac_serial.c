// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "kmac_regs.h"

/**
 * OpenTitan program for side-channel analysis of the absorb step of a KMAC128
 * operation using a 128-bit key.
 *
 * This program implements the following simple serial commands:
 *   - Set key ('k')*,
 *   - Absorb ('p')*,
 *   - FvsR batch absorb ('b')*,
 *   - FvsR batch fixed key set ('t')*,
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library. See
 * https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Key length in bytes.
   */
  kKeyLength = 16,
  /**
   * Message length in bytes.
   */
  kMessageLength = 16,
  /**
   * Digest length in 32-bit words.
   */
  kDigestLength = 8,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during SHA3 operations. Caution: This number should be chosen to
   * provide enough time. Otherwise, Ibex might wake up while SHA3 is still busy
   * and disturb the capture. Currently, we use a start trigger delay of 320
   * clock cycles and the scope captures 160 clock cycles at kClockFreqCpuHz
   * (3200 samples). On the scope side, an offset of 395 clock cycles (7900
   * samples) is used to ignore 1) the start trigger delay for the PROCESS
   * command, and 2) the absorb phase for the fixed prefix.
   */
  kIbexSha3SleepCycles = 1180,
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 128,
};

/**
 * A handle to KMAC.
 */
static dif_kmac_t kmac;

/**
 * KMAC operation state.
 */
static dif_kmac_operation_state_t kmac_operation_state;

/**
 * KMAC key.
 *
 * Used for caching the key in the 'k' (set key) command packet until it is used
 * when handling a 'p' (absorb) command.
 */
static dif_kmac_key_t kmac_key;

/**
 * KMAC fixed key.
 *
 * Used for caching the fixed key in the 't' (set fixed key) command packet
 * until it is used when handling a 'b' (batch capture) command.
 */
uint8_t key_fixed[kKeyLength];

/**
 * Fixed-key indicator.
 *
 * Used in the 'b' (batch capture) command for indicating whether to use fixed
 * or random key.
 */
static bool run_fixed = false;

/**
 * An array of keys to be used in a batch
 */
uint8_t batch_keys[kNumBatchOpsMax][kKeyLength];

/**
 * An array of messages to be used in a batch
 */
uint8_t batch_messages[kNumBatchOpsMax][kMessageLength];

/**
 * Blocks until KMAC is idle.
 */
static void kmac_block_until_idle(void) {
  // TODO(#7842): Remove when `dif_kmac_get_status()` is implemented.
  uint32_t reg;
  do {
    reg = mmio_region_read32(kmac.base_addr, KMAC_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, KMAC_STATUS_SHA3_IDLE_BIT));
}

/**
 * Resets KMAC to idle state.
 */
static void kmac_reset(void) {
  // TODO(#7842): Remove when `dif_kmac_reset()` is implemented.
  mmio_region_write32(
      kmac.base_addr, KMAC_CMD_REG_OFFSET,
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_DONE));
  kmac_block_until_idle();
}

/**
 * Report whether the hardware is currently idle.
 *
 * If the hardware is not idle then the `CFG` register is locked.
 *
 * @param params Hardware parameters.
 * @returns Whether the hardware is currently idle or not.
 */
static bool is_state_idle(void) {
  uint32_t reg = mmio_region_read32(kmac.base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_IDLE_BIT);
}

/**
 * Calculate the rate (r) in bits from the given security level.
 *
 * @param security_level Security level in bits.
 * @returns Rate in bits.
 */
static uint32_t calculate_rate_bits(uint32_t security_level) {
  // Formula for the rate in bits is:
  //
  //   r = 1600 - c
  //
  // Where c is the capacity (the security level in bits multiplied by two).
  return 1600 - 2 * security_level;
}

/**
 * Starts KMAC message without sending START command.
 *
 * Based on dif_kmac_mode_kmac_start().
 *
 * Unlike dif_kmac_mode_kmac_start(), this function doesn't provide the START
 * command to the hardware, i.e., just the key is provided and the initial setup
 * for starting a new message is performed.
 */
static dif_result_t kmac_msg_start(dif_kmac_mode_kmac_t mode, size_t l,
                                   const dif_kmac_key_t *k,
                                   const dif_kmac_customization_string_t *s) {
  if (k == NULL || l > kDifKmacMaxOutputLenWords) {
    return kDifBadArg;
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeCshakeLen128:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128;
      kmac_operation_state.r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeCshakeLen256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      kmac_operation_state.r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifBadArg;
  }
  kmac_operation_state.offset = 0;
  kmac_operation_state.d = l;
  kmac_operation_state.append_d = true;

  uint32_t key_len;
  switch (k->length) {
    case kDifKmacKeyLen128:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY128;
      break;
    case kDifKmacKeyLen192:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY192;
      break;
    case kDifKmacKeyLen256:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY256;
      break;
    case kDifKmacKeyLen384:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY384;
      break;
    case kDifKmacKeyLen512:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY512;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle()) {
    return kDifError;
  }

  // Set key length and shares.
  // Uniform sharing is achieved by XORing a random number into both shares.
  mmio_region_write32(kmac.base_addr, KMAC_KEY_LEN_REG_OFFSET, key_len);
  for (int i = 0; i < ARRAYSIZE(k->share0); ++i) {
    // Run LFSR for 32 steps to ensure that all state bits are updated.
    const uint32_t a = sca_next_lfsr(32);
    mmio_region_write32(kmac.base_addr,
                        KMAC_KEY_SHARE0_0_REG_OFFSET +
                            (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                        k->share0[i] ^ a);
    mmio_region_write32(kmac.base_addr,
                        KMAC_KEY_SHARE1_0_REG_OFFSET +
                            (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                        k->share1[i] ^ a);
  }

  // Configure cSHAKE mode with the given strength and enable KMAC mode.
  uint32_t cfg_reg =
      mmio_region_read32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, true);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Initialize prefix registers with function name ("KMAC") and empty
  // customization string. The empty customization string will be overwritten if
  // a non-empty string is provided.
  uint32_t prefix_regs[11] = {
      0x4D4B2001,  //  1  32  'K' 'M'
      0x00014341,  // 'A' 'C'  1   0
  };

  // Encoded customization string (s) must be at least 3 bytes long if it is not
  // the empty string.
  if (s != NULL && s->length >= 3) {
    // First two bytes overwrite the pre-encoded empty customization string.
    prefix_regs[1] &= 0xFFFF;
    prefix_regs[1] |= (uint32_t)((uint8_t)s->buffer[0]) << 16;
    prefix_regs[1] |= (uint32_t)((uint8_t)s->buffer[1]) << 24;
    memcpy(&prefix_regs[2], &s->buffer[2], s->length - 2);
  }

  // Write PREFIX register values.
  const mmio_region_t base = kmac.base_addr;
  mmio_region_write32(base, KMAC_PREFIX_0_REG_OFFSET, prefix_regs[0]);
  mmio_region_write32(base, KMAC_PREFIX_1_REG_OFFSET, prefix_regs[1]);
  mmio_region_write32(base, KMAC_PREFIX_2_REG_OFFSET, prefix_regs[2]);
  mmio_region_write32(base, KMAC_PREFIX_3_REG_OFFSET, prefix_regs[3]);
  mmio_region_write32(base, KMAC_PREFIX_4_REG_OFFSET, prefix_regs[4]);
  mmio_region_write32(base, KMAC_PREFIX_5_REG_OFFSET, prefix_regs[5]);
  mmio_region_write32(base, KMAC_PREFIX_6_REG_OFFSET, prefix_regs[6]);
  mmio_region_write32(base, KMAC_PREFIX_7_REG_OFFSET, prefix_regs[7]);
  mmio_region_write32(base, KMAC_PREFIX_8_REG_OFFSET, prefix_regs[8]);
  mmio_region_write32(base, KMAC_PREFIX_9_REG_OFFSET, prefix_regs[9]);
  mmio_region_write32(base, KMAC_PREFIX_10_REG_OFFSET, prefix_regs[10]);

  return kDifOk;
}

/**
 * Writes the message including its length to the message FIFO.
 *
 * Based on dif_kmac_absorb().
 *
 * Unlike dif_kmac_absorb(), this function 1) doesn't require the hardware
 * to enter the 'absorb' state before writing the message into the message
 * FIFO, and 2) appends the output length afterwards (normally done as
 * part of dif_kmac_squeeze()).
 */
static dif_result_t kmac_msg_write(const void *msg, size_t msg_len,
                                   size_t *processed) {
  // Set the number of bytes processed to 0.
  if (processed != NULL) {
    *processed = 0;
  }

  if (msg == NULL && msg_len != 0) {
    return kDifBadArg;
  }

  // Check that an operation has been started.
  if (kmac_operation_state.r == 0) {
    return kDifError;
  }

  // Copy the message one byte at a time.
  // This could be sped up copying a word at a time but be careful
  // about message endianness (e.g. only copy a word at a time when in
  // little-endian mode).
  for (size_t i = 0; i < msg_len; ++i) {
    mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                       ((const uint8_t *)msg)[i]);
  }

  if (processed != NULL) {
    *processed = msg_len;
  }

  // The KMAC operation requires that the output length (d) in bits be right
  // encoded and appended to the end of the message.
  // Note: kDifKmacMaxOutputLenWords could be reduced to make this code
  // simpler. For example, a maximum of `(UINT16_MAX - 32) / 32` (just under
  // 8 KiB) would mean that d is guaranteed to be less than 0xFFFF.
  uint32_t d = kmac_operation_state.d * 32;
  int out_len = 1 + (d > 0xFF) + (d > 0xFFFF) + (d > 0xFFFFFF);
  int shift = (out_len - 1) * 8;
  while (shift >= 8) {
    mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                       (uint8_t)(d >> shift));
    shift -= 8;
  }
  mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)d);
  mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                     (uint8_t)out_len);
  kmac_operation_state.squeezing = true;

  return kDifOk;
}

/**
 * Starts actual processing of a previously provided message.
 *
 * This function issues a START command directly followed by a PROCESS command.
 */
static void kmac_msg_proc(void) {
  // Issue START command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Issue PROCESS command.
  cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_PROCESS);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);
}

/**
 * Waits until the hardware enters the 'squeeze' state.
 *
 * If the hardware enters the `squeeze` state, this means the output state is
 * valid and can be read by software.
 */
static void kmac_msg_done(void) {
  // TODO(#7841, #7842): Remove when we finalize the way we capture traces.
  uint32_t reg;
  do {
    reg = mmio_region_read32(kmac.base_addr, KMAC_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, KMAC_STATUS_SHA3_SQUEEZE_BIT));
}

/**
 * Reads the digest from the hardware.
 *
 * Based on dif_kmac_squeeze().
 *
 * Unlike dif_kmac_squeeze(), this function 1) doesn't wait until the hardware
 * enters the 'squeeze' state, 2) doesn't append the output length, 3) doesn't
 * support the generation of more state.
 */
static dif_result_t kmac_get_digest(uint32_t *out, size_t len) {
  if (out == NULL && len != 0) {
    return kDifBadArg;
  }

  while (len > 0) {
    size_t n = len;
    size_t remaining = kmac_operation_state.r - kmac_operation_state.offset;
    if (kmac_operation_state.d != 0 &&
        kmac_operation_state.d < kmac_operation_state.r) {
      remaining = kmac_operation_state.d - kmac_operation_state.offset;
    }
    if (n > remaining) {
      n = remaining;
    }
    if (n == 0) {
      // Normally, the hardware would now have to generate more state. But
      // since at this point, the power measurement is already stopped, we don't
      // support that here.
      return kDifError;
    }

    ptrdiff_t offset =
        KMAC_STATE_REG_OFFSET +
        (ptrdiff_t)kmac_operation_state.offset * (ptrdiff_t)sizeof(uint32_t);
    for (size_t i = 0; i < n; ++i) {
      // Read both shares from state register and combine using XOR.
      uint32_t share0 = mmio_region_read32(kmac.base_addr, offset);
      uint32_t share1 =
          mmio_region_read32(kmac.base_addr, offset + kDifKmacStateShareOffset);
      *out++ = share0 ^ share1;
      offset += sizeof(uint32_t);
    }
    kmac_operation_state.offset += n;
    len -= n;
  }
  return kDifOk;
}

/**
 * Initializes the KMAC peripheral.
 *
 * This function configures KMAC to use software entropy.
 */
static void kmac_init(void) {
  SS_CHECK_DIF_OK(dif_kmac_init(
      mmio_region_from_addr(TOP_DARJEELING_KMAC_BASE_ADDR), &kmac));

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .message_big_endian = kDifToggleDisabled,
      .output_big_endian = kDifToggleDisabled,
      .sideload = kDifToggleDisabled,
      .msg_mask = kDifToggleEnabled,
  };
  SS_CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  kmac_block_until_idle();
}

/**
 * Simple serial 'k' (set key) command handler.
 *
 * This function simply caches the provided key in the static `kmac_key`
 * variable so that it can be used in subsequent operations. This function does
 * not use key shares to simplify side-channel analysis. The key must be
 * `kKeyLength` bytes long.
 *
 * @param key Key. Must be `kKeyLength` bytes long.
 * @param key_len Key length. Must be equal to `kKeyLength`.
 * @return Result of the operation.
 */
static void sha3_serial_set_key(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kKeyLength);

  kmac_key = (dif_kmac_key_t){
      .length = kDifKmacKeyLen128,
  };
  memcpy(kmac_key.share0, key, kKeyLength);
}

/**
 * Absorbs a message using KMAC128 without a customization string.
 *
 * @param msg Message.
 * @param msg_len Message length.
 */
static void sha3_serial_absorb(const uint8_t *msg, size_t msg_len) {
  // Start a new message and write data to message FIFO.
  SS_CHECK_DIF_OK(
      kmac_msg_start(kDifKmacModeKmacLen128, kDigestLength, &kmac_key, NULL));
  SS_CHECK_DIF_OK(kmac_msg_write(msg, msg_len, NULL));

  // Start the SHA3 processing (this triggers the capture) and go to sleep.
  // Using the SecCmdDelay hardware parameter, the KMAC unit is
  // configured to start operation 40 cycles after receiving the START and PROC
  // commands. This allows Ibex to go to sleep in order to not disturb the
  // capture.
  sca_call_and_sleep(kmac_msg_proc, kIbexSha3SleepCycles);
}

/**
 * Simple serial 'p' (absorb) command handler.
 *
 * Absorbs the given message using KMAC128 without a customization string,
 * and sends the digest over UART. This function also handles the trigger
 * signal.
 *
 * @param msg Message.
 * @param msg_len Message length.
 */
static void sha3_serial_single_absorb(const uint8_t *msg, size_t msg_len) {
  SS_CHECK(msg_len == kMessageLength);

  // Ungate the capture trigger signal and then start the operation.
  sca_set_trigger_high();
  sha3_serial_absorb(msg, msg_len);
  sca_set_trigger_low();

  // Check KMAC has finsihed processing the message.
  kmac_msg_done();

  // Read the digest and send it to the host for verification.
  uint32_t out[kDigestLength];
  SS_CHECK_DIF_OK(kmac_get_digest(out, kDigestLength));
  simple_serial_send_packet('r', (uint8_t *)out, kDigestLength * 4);

  // Reset before the next absorb since KMAC must be idle before starting
  // another absorb.
  kmac_reset();
}

static void sha3_serial_fixed_key_set(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kKeyLength);
  memcpy(key_fixed, key, key_len);
}

static void sha3_serial_batch(const uint8_t *data, size_t data_len) {
  uint32_t num_encryptions = 0;
  uint32_t out[kDigestLength];
  uint32_t batch_digest[kDigestLength];
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);

  for (uint32_t j = 0; j < kDigestLength; ++j) {
    batch_digest[j] = 0;
  }

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    if (run_fixed) {
      memcpy(batch_keys[i], key_fixed, kKeyLength);
    } else {
      prng_rand_bytes(batch_keys[i], kKeyLength);
    }
    prng_rand_bytes(batch_messages[i], kMessageLength);
    run_fixed = batch_messages[i][0] & 0x1;
  }

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    kmac_reset();
    memcpy(kmac_key.share0, batch_keys[i], kKeyLength);

    sca_set_trigger_high();
    sha3_serial_absorb(batch_messages[i], kMessageLength);
    sca_set_trigger_low();

    kmac_msg_done();
    SS_CHECK_DIF_OK(kmac_get_digest(out, kDigestLength));

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all outputs of
    // the batch.
    for (uint32_t j = 0; j < kDigestLength; ++j) {
      batch_digest[j] ^= out[j];
    }
  }
  // Send the batch digest to the host for verification.
  simple_serial_send_packet('r', (uint8_t *)batch_digest, kDigestLength * 4);
}

/**
 * Simple serial 'l' (seed lfsr) command handler.
 *
 * This function only supports 4-byte seeds.
 *
 * @param seed A buffer holding the seed.
 */
static void sha3_serial_seed_lfsr(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == sizeof(uint32_t));
  sca_seed_lfsr(read_32(seed));
}

/**
 * Main function.
 *
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
bool test_main(void) {
  sca_init(kScaTriggerSourceKmac, kScaPeripheralIoDiv4 | kScaPeripheralKmac);

  LOG_INFO("Running kmac_serial");

  LOG_INFO("Initializing simple serial interface to capture board.");
  simple_serial_init(sca_get_uart());
  simple_serial_register_handler('k', sha3_serial_set_key);
  simple_serial_register_handler('p', sha3_serial_single_absorb);
  simple_serial_register_handler('b', sha3_serial_batch);
  simple_serial_register_handler('f', sha3_serial_fixed_key_set);
  simple_serial_register_handler('l', sha3_serial_seed_lfsr);

  LOG_INFO("Initializing the KMAC peripheral.");
  kmac_init();

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}
