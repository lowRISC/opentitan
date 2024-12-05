// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/kmac_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/kmac_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

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
   * clock cycles and the scope captures 160 clock cycles at kClockFreqCpuHz.
   * On the scope side, an offset of 395 clock cycles is used to ignore 1) the
   * start trigger delay for the PROCESS command, and 2) the absorb phase for
   * the fixed prefix.
   */
  kIbexSha3SleepCycles = 1180,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during loading and hashing the prefix as well as loading and hashing
   * the key.
   */
  kIbexLoadHashPrefixKeySleepCycles = 300,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during loading and hashing the message.
   */
  kIbexLoadHashMessageSleepCycles = 500,
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 128,
};

/**
 * Enable FPGA mode.
 */
static bool fpga_mode = false;

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
uint8_t kmac_batch_keys[kNumBatchOpsMax][kKeyLength];

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
static kmac_sca_error_t kmac_msg_start(
    dif_kmac_mode_kmac_t mode, size_t l, const dif_kmac_key_t *k,
    const dif_kmac_customization_string_t *s) {
  if (k == NULL || l > kDifKmacMaxOutputLenWords) {
    return kmacScaOutOfRange;
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
      return kmacScaOutOfRange;
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
      return kmacScaOutOfRange;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle()) {
    return kmacScaAborted;
  }

  // Set key length and shares.
  // Uniform sharing is achieved by XORing a random number into both shares.
  mmio_region_write32(kmac.base_addr, KMAC_KEY_LEN_REG_OFFSET, key_len);
  for (int i = 0; i < ARRAYSIZE(k->share0); ++i) {
    // Run LFSR for 32 steps to ensure that all state bits are updated.
    const uint32_t a = pentest_next_lfsr(32, kPentestLfsrMasking);
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

  return kmacScaOk;
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
static kmac_sca_error_t kmac_msg_write(const void *msg, size_t msg_len,
                                       size_t *processed) {
  // Set the number of bytes processed to 0.
  if (processed != NULL) {
    *processed = 0;
  }

  if (msg == NULL && msg_len != 0) {
    return kmacScaOutOfRange;
  }

  // Check that an operation has been started.
  if (kmac_operation_state.r == 0) {
    return kmacScaAborted;
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

  return kmacScaOk;
}

/**
 * Starts actual processing of a previously provided message.
 *
 * This function issues a PROCESS command.
 */
static void kmac_process_cmd(void) {
  // Issue PROCESS command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_PROCESS);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);
}

/**
 * Prepares KMAC to receive the message via the FIFO.
 *
 * This function issues a START command.
 */
static void kmac_start_cmd(void) {
  // Issue START command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);
}

/**
 * Starts actual processing of a previously provided message.
 *
 * This function issues a START command directly followed by a PROCESS command.
 */
static void kmac_start_process_cmd(void) {
  // Issue START command.
  kmac_start_cmd();

  // Issue PROCESS command.
  kmac_process_cmd();
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
kmac_sca_error_t kmac_get_digest(uint32_t *out, size_t len) {
  if (out == NULL && len != 0) {
    return kmacScaOutOfRange;
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
      return kmacScaAborted;
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
  return kmacScaOk;
}

/**
 * Initializes the KMAC peripheral.
 *
 * This function configures KMAC to use software entropy.
 */
status_t handle_kmac_pentest_init(ujson_t *uj) {
  // Read mode. FPGA or discrete.
  cryptotest_kmac_sca_fpga_mode_t uj_data;
  TRY(ujson_deserialize_cryptotest_kmac_sca_fpga_mode_t(uj, &uj_data));
  if (uj_data.fpga_mode == 0x01) {
    fpga_mode = true;
  }
  // Setup the trigger.
  pentest_init(kPentestTriggerSourceKmac,
               kPentestPeripheralIoDiv4 | kPentestPeripheralKmac);
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .message_big_endian = kDifToggleDisabled,
      .output_big_endian = kDifToggleDisabled,
      .sideload = kDifToggleDisabled,
      .msg_mask = kDifToggleEnabled,
  };
  TRY(dif_kmac_configure(&kmac, config));

  kmac_block_until_idle();

  // Disable the instruction cache and dummy instructions for better SCA
  // measurements.
  pentest_configure_cpu();

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  return OK_STATUS();
}

/**
 * Set key command handler.
 *
 * This function simply caches the provided key in the static `kmac_key`
 * variable so that it can be used in subsequent operations. This function does
 * not use key shares to simplify side-channel analysis. The key must be
 * `kKeyLength` bytes long.
 *
 * The uJSON data contains:
 *  - key Key. Must be `kKeyLength` bytes long.
 *  - key_len Key length. Must be equal to `kKeyLength`.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_sca_set_key(ujson_t *uj) {
  cryptotest_kmac_sca_key_t uj_key;
  TRY(ujson_deserialize_cryptotest_kmac_sca_key_t(uj, &uj_key));

  if (uj_key.key_length != kKeyLength) {
    return OUT_OF_RANGE();
  }

  kmac_key = (dif_kmac_key_t){
      .length = kDifKmacKeyLen128,
  };
  memcpy(kmac_key.share0, uj_key.key, kKeyLength);

  return OK_STATUS();
}

/**
 * Absorbs a message using KMAC128 without a customization string.
 *
 * Two modes are supported: FPGA and non-FPGA mode.
 * The FPGA mode can be used to improve KMAC SCA. Here, features only available
 * on the FPGA bitstream are used (i.e., SecKmacCmdDelay and
 * SecKmacIdleAcceptSwMsg). The non-FPGA mode represents the chip where these
 * features are disabled.
 *
 * In the FPGA mode, this function performs:
 * - Configure mode/key/...
 * - Write data to the message FIFO.
 * - Send START and PROCESS commands, put Ibex into sleep.
 *
 * In the non-FPGA mode, this function performs:
 * - Configure mode/key/...
 * - Send START command, put Ibex into sleep.
 * - Write message FIFO.
 * - Send PROCESS command, put Ibex into sleep.
 *
 * @param msg Message.
 * @param msg_len Message length.
 */
static kmac_sca_error_t sha3_ujson_absorb(const uint8_t *msg, size_t msg_len) {
  // Start a new message.
  if (kmac_msg_start(kDifKmacModeKmacLen128, kDigestLength, &kmac_key, NULL) !=
      kmacScaOk) {
    return kmacScaAborted;
  }

  if (fpga_mode == false) {
    // Start command. On the chip, we need to first issue a START command
    // before writing to the message FIFO.
    pentest_call_and_sleep(kmac_start_cmd, kIbexLoadHashPrefixKeySleepCycles,
                           false, false);
  }

  // Write data to message FIFO.
  if (kmac_msg_write(msg, msg_len, NULL) != kmacScaOk) {
    return kmacScaAborted;
  }

  if (fpga_mode) {
    // On the FPGA, start the SHA3 processing (this triggers the capture) and
    // go to sleep. Using the SecCmdDelay hardware parameter, the KMAC unit is
    // configured to start operation 320 cycles after receiving the START and
    // PROC commands. This allows Ibex to go to sleep in order to not disturb
    // the capture.
    pentest_call_and_sleep(kmac_start_process_cmd, kIbexSha3SleepCycles, false,
                           false);
  } else {
    // On the chip, issue a PROCESS command to start operation and put Ibex
    // into sleep.
    pentest_call_and_sleep(kmac_process_cmd, kIbexLoadHashMessageSleepCycles,
                           false, false);
  }

  return kmacScaOk;
}

/**
 * Absorb command handler.
 *
 * Absorbs the given message using KMAC128 without a customization string,
 * and sends the digest over UART. This function also handles the trigger
 * signal.
 *
 * The uJSON data contains:
 *  - msg: Message.
 *  - msg_len: Message length.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_sca_single_absorb(ujson_t *uj) {
  cryptotest_kmac_sca_msg_t uj_msg;
  TRY(ujson_deserialize_cryptotest_kmac_sca_msg_t(uj, &uj_msg));

  if (uj_msg.msg_length != kMessageLength) {
    return OUT_OF_RANGE();
  }

  // Ungate the capture trigger signal and then start the operation.
  pentest_set_trigger_high();
  if (sha3_ujson_absorb(uj_msg.msg, uj_msg.msg_length) != kmacScaOk) {
    return ABORTED();
  }
  pentest_set_trigger_low();

  // Check KMAC has finished processing the message.
  kmac_msg_done();

  // Read the digest and send it to the host for verification.
  uint32_t out[kDigestLength];
  if (kmac_get_digest(out, kDigestLength) != kmacScaOk) {
    return ABORTED();
  }

  cryptotest_kmac_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)out, kDigestLength * 4);
  RESP_OK(ujson_serialize_cryptotest_kmac_sca_batch_digest_t, uj, &uj_output);

  // Reset before the next absorb since KMAC must be idle before starting
  // another absorb.
  kmac_reset();

  return OK_STATUS();
}

/**
 * Fixed key set command handler.
 *
 *  * The uJSON data contains:
 *  - key: The key to use.
 *  - key_length: The length of the key.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_sca_fixed_key_set(ujson_t *uj) {
  cryptotest_kmac_sca_key_t uj_key;
  TRY(ujson_deserialize_cryptotest_kmac_sca_key_t(uj, &uj_key));

  if (uj_key.key_length != kKeyLength) {
    return OUT_OF_RANGE();
  }

  memcpy(key_fixed, uj_key.key, uj_key.key_length);

  return OK_STATUS();
}

/**
 * Batch command handler.
 *
 * Start batch mode.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_sca_batch(ujson_t *uj) {
  cryptotest_kmac_sca_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_kmac_sca_data_t(uj, &uj_data));

  uint32_t num_encryptions = 0;
  uint32_t out[kDigestLength];
  uint32_t batch_digest[kDigestLength];

  num_encryptions = read_32(uj_data.data);

  for (uint32_t j = 0; j < kDigestLength; ++j) {
    batch_digest[j] = 0;
  }

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    if (run_fixed) {
      memcpy(kmac_batch_keys[i], key_fixed, kKeyLength);
    } else {
      prng_rand_bytes(kmac_batch_keys[i], kKeyLength);
    }
    prng_rand_bytes(batch_messages[i], kMessageLength);
    run_fixed = batch_messages[i][0] & 0x1;
  }

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    kmac_reset();
    memcpy(kmac_key.share0, kmac_batch_keys[i], kKeyLength);

    pentest_set_trigger_high();
    if (sha3_ujson_absorb(batch_messages[i], kMessageLength) != kmacScaOk) {
      return ABORTED();
    }
    pentest_set_trigger_low();

    kmac_msg_done();
    if (kmac_get_digest(out, kDigestLength) != kmacScaOk) {
      return ABORTED();
    }

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all outputs of
    // the batch.
    for (uint32_t j = 0; j < kDigestLength; ++j) {
      batch_digest[j] ^= out[j];
    }
  }
  // Send the batch digest to the host for verification.
  cryptotest_kmac_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest, kDigestLength * 4);
  RESP_OK(ujson_serialize_cryptotest_kmac_sca_batch_digest_t, uj, &uj_output);

  return OK_STATUS();
}

/**
 * Seed lfsr command handler.
 *
 * This function only supports 4-byte seeds.
 *
 *  * The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_pentest_seed_lfsr(ujson_t *uj) {
  cryptotest_kmac_sca_lfsr_t uj_lfsr_data;
  TRY(ujson_deserialize_cryptotest_kmac_sca_lfsr_t(uj, &uj_lfsr_data));
  pentest_seed_lfsr(read_32(uj_lfsr_data.seed), kPentestLfsrMasking);

  return OK_STATUS();
}

/**
 * Ibex FI command handler.
 *
 * Command handler for the Ibex FI command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_kmac_sca(ujson_t *uj) {
  kmac_sca_subcommand_t cmd;
  TRY(ujson_deserialize_kmac_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kKmacScaSubcommandInit:
      return handle_kmac_pentest_init(uj);
    case kKmacScaSubcommandSetKey:
      return handle_kmac_sca_set_key(uj);
    case kKmacScaSubcommandSingleAbsorb:
      return handle_kmac_sca_single_absorb(uj);
    case kKmacScaSubcommandBatch:
      return handle_kmac_sca_batch(uj);
    case kKmacScaSubcommandFixedKeySet:
      return handle_kmac_sca_fixed_key_set(uj);
    case kKmacScaSubcommandSeedLfsr:
      return handle_kmac_pentest_seed_lfsr(uj);
    default:
      LOG_ERROR("Unrecognized KMAC SCA FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
