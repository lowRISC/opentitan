// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

/**
 * OpenTitan program for side-channel analysis of the absorb step of a KMAC128
 * operation using a 128-bit key.
 *
 * This program implements the following simple serial commands:
 *   - Set key ('k')*,
 *   - Absorb ('p')*,
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library. See
 * https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

enum {
  /**
   * Key length in bytes.
   */
  kKeyLength = 16,
  /**
   * Message length in bytes.
   */
  kMessageLength = 16,
};

/**
 * A handle to KMAC.
 */
static dif_kmac_t kmac;

/**
 * KMAC key.
 *
 * Used for caching the key in the 'k' (set key) command packet until it is used
 * when handling a 'p' (absorb) command.
 */
static dif_kmac_key_t kmac_key;

/**
 * Blocks until KMAC is idle.
 */
static void kmac_block_until_idle(void) {
  // TODO(#7842): Remove when `dif_kmac_get_status()` is implemented.
  uint32_t reg;
  do {
    reg = mmio_region_read32(kmac.params.base_addr, KMAC_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, KMAC_STATUS_SHA3_IDLE_BIT));
}

/**
 * Resets KMAC to idle state.
 */
static void kmac_reset(void) {
  // TODO(#7842): Remove when `dif_kmac_reset()` is implemented.
  mmio_region_write32(
      kmac.params.base_addr, KMAC_CMD_REG_OFFSET,
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_DONE));
  kmac_block_until_idle();
}

/**
 * Issues a process command to KMAC and waits until absorb step is complete.
 */
static void kmac_absorb_end(void) {
  // TODO(#7841, #7842): Remove when we finalize the way we capture traces.
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, KMAC_CMD_CMD_FIELD,
                               KMAC_CMD_CMD_VALUE_PROCESS);
  mmio_region_write32(kmac.params.base_addr, KMAC_CMD_REG_OFFSET, reg);

  do {
    reg = mmio_region_read32(kmac.params.base_addr, KMAC_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, KMAC_STATUS_SHA3_SQUEEZE_BIT));
}

/**
 * Initializes the KMAC peripheral.
 *
 * This function configures KMAC to use software entropy.
 */
static void kmac_init(void) {
  dif_kmac_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR),
  };
  CHECK(dif_kmac_init(params, &kmac) == kDifKmacOk);

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = 0xffff,
      .entropy_fast_process = true,
  };
  CHECK(dif_kmac_configure(&kmac, config) == kDifKmacOk);

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
 * Simple serial 'p' (absorb) command handler.
 *
 * Absorbs the given message using KMAC128 without a customization string.
 *
 * @param msg Message.
 * @param msg_len Message length.
 */
static void sha3_serial_single_absorb(const uint8_t *msg, size_t msg_len) {
  SS_CHECK(msg_len == kMessageLength);

  SS_CHECK(dif_kmac_mode_kmac_start(&kmac, kDifKmacModeKmacLen128, 0, &kmac_key,
                                    NULL) == kDifKmacOk);

  // TODO(#7841): Consider delaying the absorb step until triggered manually to
  // be able to use `sca_call_and_sleep()`.
  sca_set_trigger_high();
  SS_CHECK(dif_kmac_absorb(&kmac, msg, msg_len, NULL) == kDifKmacOk);
  // Note: Performing the squeeze step after this call using HW directly would
  // produce incorrect results. See `dif_kmac_mode_kmac_start()` and
  // `dif_kmac_squeeze()`.
  kmac_absorb_end();
  sca_set_trigger_low();

  // Reset before the next absorb since KMAC must be idle before starting
  // another absorb.
  kmac_reset();
}

/**
 * Main function.
 *
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
int main(void) {
  const dif_uart_t *uart1;

  sca_init(kScaTriggerSourceKmac, kScaPeripheralKmac);

  LOG_INFO("Running sha3_serial");

  LOG_INFO("Initializing simple serial interface to capture board.");
  sca_get_uart(&uart1);
  simple_serial_init(uart1);
  simple_serial_register_handler('k', sha3_serial_set_key);
  simple_serial_register_handler('p', sha3_serial_single_absorb);

  LOG_INFO("Initializing the KMAC peripheral.");
  kmac_init();

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}
