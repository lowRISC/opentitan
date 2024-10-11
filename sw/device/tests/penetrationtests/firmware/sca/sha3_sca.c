// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/sha3_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/sha3_sca_commands.h"

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
   * clock cycles and the scope captures 120 clock cycles at kClockFreqCpuHz.
   * On the scope side, an offset of 320 clock cycles can be used to ignore the
   * start trigger delay for the PROCESS command.
   */
  kIbexSha3SleepCycles = 1060,
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
 * The KMAC config.
 */
static dif_kmac_config_t config = (dif_kmac_config_t){
    .entropy_mode = kDifKmacEntropyModeSoftware,
    .entropy_fast_process = kDifToggleDisabled,
    .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba, 0x50dc409c,
                     0x11e1ebd1},
    .message_big_endian = kDifToggleDisabled,
    .output_big_endian = kDifToggleDisabled,
    .sideload = kDifToggleDisabled,
    .msg_mask = kDifToggleEnabled,
};

/**
 * KMAC operation state.
 */
static dif_kmac_operation_state_t kmac_operation_state;

/**
 * SHA3 fixed message.
 *
 * Used for caching the fixed key in the 't' (set fixed key) command packet
 * until it is used when handling a 'b' (batch capture) command.
 */
uint8_t message_fixed[kMessageLength];

/**
 * Fixed-message indicator.
 *
 * Used in the 'b' (batch capture) command for indicating whether to use fixed
 * or random message.
 */
static bool run_fixed = false;

/**
 * An array of messages to be used in a batch
 */
uint8_t sha3_batch_messages[kNumBatchOpsMax][kMessageLength];

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
 * Starts KMAC/SHA3 message without sending START command.
 *
 * Based on dif_kmac_mode_sha3_start().
 *
 * Unlike dif_kmac_mode_sha3_start(), this function doesn't provide the START
 * command to the hardware.
 */
static dif_result_t sha3_msg_start(dif_kmac_mode_sha3_t mode) {
  // Set kstrength and calculate rate (r) and digest length (d) in 32-bit
  // words.
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeSha3Len224:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224;
      kmac_operation_state.offset = 0;
      kmac_operation_state.r = calculate_rate_bits(224) / 32;
      kmac_operation_state.d = 224 / 32;
      break;
    case kDifKmacModeSha3Len256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      kmac_operation_state.offset = 0;
      kmac_operation_state.r = calculate_rate_bits(256) / 32;
      kmac_operation_state.d = 256 / 32;
      break;
    case kDifKmacModeSha3Len384:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384;
      kmac_operation_state.offset = 0;
      kmac_operation_state.r = calculate_rate_bits(384) / 32;
      kmac_operation_state.d = 384 / 32;
      break;
    case kDifKmacModeSha3Len512:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512;
      kmac_operation_state.offset = 0;
      kmac_operation_state.r = calculate_rate_bits(512) / 32;
      kmac_operation_state.d = 512 / 32;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle()) {
    return kDifError;
  }

  kmac_operation_state.squeezing = false;
  kmac_operation_state.append_d = false;

  // Configure SHA-3 mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

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
static dif_result_t sha3_msg_write(const void *msg, size_t msg_len,
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
  kmac_operation_state.squeezing = true;

  return kDifOk;
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
 * Prepare to receive message via the FIFO.
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
static dif_result_t sha3_get_digest(uint32_t *out, size_t len) {
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
 * Disables/Enables masking in the KMAC/SHA3 peripheral.
 *
 * This function configures KMAC/SHA3 with the appropriate mask setting.
 */
status_t handle_sha3_sca_disable_masking(ujson_t *uj) {
  cryptotest_sha3_sca_masks_off_t uj_data;
  TRY(ujson_deserialize_cryptotest_sha3_sca_masks_off_t(uj, &uj_data));

  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  if (uj_data.masks_off == 0x01) {
    config.entropy_fast_process = kDifToggleEnabled;
    config.msg_mask = kDifToggleDisabled;
  } else {
    config.entropy_fast_process = kDifToggleDisabled;
    config.msg_mask = kDifToggleEnabled;
  }
  TRY(dif_kmac_configure(&kmac, config));

  kmac_block_until_idle();
  // Acknowledge the command. This is crucial to be in sync with the host.
  cryptotest_sha3_sca_status_t uj_status;
  uj_status.status = 0;
  RESP_OK(ujson_serialize_cryptotest_sha3_sca_status_t, uj, &uj_status);

  return OK_STATUS();
}

/**
 * Absorbs a message without a customization string. Arms & disarms the trigger
 * before and after the PROCESS command is issued.
 *
 * @param msg Message.
 * @param msg_len Message length.
 */
sha3_sca_error_t sha3_serial_absorb(const uint8_t *msg, size_t msg_len) {
  // Start a new message.
  if (sha3_msg_start(kDifKmacModeSha3Len256) != kDifOk) {
    return sha3ScaAborted;
  }

  if (fpga_mode == false) {
    // Start command. On the chip, we need to first issue a START command
    // before writing to the message FIFO.
    kmac_start_cmd();
  }

  // Write data to message FIFO.
  if (sha3_msg_write(msg, msg_len, NULL) != kDifOk) {
    return sha3ScaAborted;
  }

  if (fpga_mode) {
    // Start the SHA3 processing (this triggers the capture) and go to sleep.
    // Using the SecCmdDelay hardware parameter, the KMAC unit is
    // configured to start operation 320 cycles after receiving the START and
    // PROC commands. This allows Ibex to go to sleep in order to not disturb
    // the capture.
    pentest_call_and_sleep(kmac_start_process_cmd, kIbexSha3SleepCycles, true,
                           false);
  } else {
    // On the chip, issue a PROCESS command to start operation and put Ibex
    // into sleep.
    pentest_call_and_sleep(kmac_process_cmd, kIbexLoadHashMessageSleepCycles,
                           true, false);
  }

  return sha3ScaOk;
}

/**
 * Absorb command handler.
 *
 * Absorbs the given message without a customization string,
 * and sends the digest over UART.
 *
 * The uJSON data contains:
 *  - msg: Message.
 *  - msg_length: Message length.
 * @param uj The received uJSON data.
 */
status_t handle_sha3_sca_single_absorb(ujson_t *uj) {
  cryptotest_sha3_sca_msg_t uj_msg;
  TRY(ujson_deserialize_cryptotest_sha3_sca_msg_t(uj, &uj_msg));
  if (uj_msg.msg_length != kMessageLength) {
    return OUT_OF_RANGE();
  }

  // Start the operation.
  if (sha3_serial_absorb(uj_msg.msg, uj_msg.msg_length) != sha3ScaOk) {
    return ABORTED();
  }

  // Check KMAC has finished processing the message.
  kmac_msg_done();

  // Read the digest and send it to the host for verification.
  uint32_t out[kDigestLength];
  if (sha3_get_digest(out, kDigestLength) != kDifOk) {
    return ABORTED();
  }
  cryptotest_sha3_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)out, kDigestLength * 4);
  RESP_OK(ujson_serialize_cryptotest_sha3_sca_batch_digest_t, uj, &uj_output);

  // Reset before the next absorb since KMAC must be idle before starting
  // another absorb.
  kmac_reset();

  return OK_STATUS();
}

/**
 * Fixed message set command handler.
 *
 * Set the fixed message.
 *
 * The uJSON data contains:
 *  - msg: The message to set.
 *  - msg_length: The length of the message.
 *
 * @param uj The received uJSON data.
 */
status_t handle_sha3_sca_fixed_message_set(ujson_t *uj) {
  cryptotest_sha3_sca_msg_t uj_msg;
  TRY(ujson_deserialize_cryptotest_sha3_sca_msg_t(uj, &uj_msg));

  if (uj_msg.msg_length != kMessageLength) {
    return OUT_OF_RANGE();
  }

  memcpy(message_fixed, uj_msg.msg, uj_msg.msg_length);

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
status_t handle_sha3_sca_batch(ujson_t *uj) {
  cryptotest_sha3_sca_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_sha3_sca_data_t(uj, &uj_data));

  uint32_t num_hashes = 0;
  uint32_t out[kDigestLength];
  uint32_t batch_digest[kDigestLength];
  uint8_t dummy_message[kMessageLength];
  num_hashes = read_32(uj_data.data);

  for (uint32_t j = 0; j < kDigestLength; ++j) {
    batch_digest[j] = 0;
  }

  for (uint32_t i = 0; i < num_hashes; ++i) {
    if (run_fixed) {
      memcpy(sha3_batch_messages[i], message_fixed, kMessageLength);
    } else {
      prng_rand_bytes(sha3_batch_messages[i], kMessageLength);
    }
    prng_rand_bytes(dummy_message, kMessageLength);
    run_fixed = dummy_message[0] & 0x1;
  }

  for (uint32_t i = 0; i < num_hashes; ++i) {
    kmac_reset();

    if (sha3_serial_absorb(sha3_batch_messages[i], kMessageLength) !=
        sha3ScaOk) {
      return ABORTED();
    }

    kmac_msg_done();
    if (sha3_get_digest(out, kDigestLength) != kDifOk) {
      return ABORTED();
    }

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all outputs of
    // the batch.
    for (uint32_t j = 0; j < kDigestLength; ++j) {
      batch_digest[j] ^= out[j];
    }
  }

  // Acknowledge the batch command. This is crucial to be in sync with the host
  cryptotest_sha3_sca_status_t uj_status;
  uj_status.status = 0;
  RESP_OK(ujson_serialize_cryptotest_sha3_sca_status_t, uj, &uj_status);
  // Send the batch digest to the host for verification.
  cryptotest_sha3_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest, kDigestLength * 4);
  RESP_OK(ujson_serialize_cryptotest_sha3_sca_batch_digest_t, uj, &uj_output);

  return OK_STATUS();
}

/**
 * Seed lfsr command handler.
 *
 * This function only supports 4-byte seeds.
 *
 *  The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *
 * @param uj The received uJSON data.
 */
status_t handle_sha3_sca_seed_lfsr(ujson_t *uj) {
  cryptotest_sha3_sca_lfsr_t uj_lfsr_data;
  TRY(ujson_deserialize_cryptotest_sha3_sca_lfsr_t(uj, &uj_lfsr_data));
  sca_seed_lfsr(read_32(uj_lfsr_data.seed), kScaLfsrMasking);

  return OK_STATUS();
}

/**
 * Init command handler.
 *
 * Initializes the KMAC peripheral and setups the trigger. Configures KMAC to
 * use software entropy.
 *
 * @param uj The received uJSON data.
 */
status_t handle_sha3_sca_init(ujson_t *uj) {
  // Read mode. FPGA or discrete.
  cryptotest_sha3_sca_fpga_mode_t uj_data;
  TRY(ujson_deserialize_cryptotest_sha3_sca_fpga_mode_t(uj, &uj_data));
  if (uj_data.fpga_mode == 0x01) {
    fpga_mode = true;
  }

  sca_init(kScaTriggerSourceKmac, kScaPeripheralIoDiv4 | kScaPeripheralKmac);

  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

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
 * SHA SCA command handler.
 *
 * Command handler for the SHA SCA command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_sha3_sca(ujson_t *uj) {
  sha3_sca_subcommand_t cmd;
  TRY(ujson_deserialize_sha3_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kSha3ScaSubcommandInit:
      return handle_sha3_sca_init(uj);
    case kSha3ScaSubcommandSingleAbsorb:
      return handle_sha3_sca_single_absorb(uj);
    case kSha3ScaSubcommandBatch:
      return handle_sha3_sca_batch(uj);
    case kSha3ScaSubcommandFixedMessageSet:
      return handle_sha3_sca_fixed_message_set(uj);
    case kSha3ScaSubcommandSeedLfsr:
      return handle_sha3_sca_seed_lfsr(uj);
    case kSha3ScaSubcommandDisableMasking:
      return handle_sha3_sca_disable_masking(uj);
    default:
      LOG_ERROR("Unrecognized SHA SCA FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
