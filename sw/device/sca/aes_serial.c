// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * OpenTitan program for AES side-channel analysis.
 *
 * This program implements the following simple serial commands:
 *   - Set key ('k')*,
 *   - Encrypt ('p')*,
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 *   - Batch encrypt ('b')*,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library. Encryption is done in AES-ECB-128
 * mode. See https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

enum {
  kAesKeyLength = 16,
  kAesTextLength = 16,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during AES operations. Caution: This number should be chosen to
   * provide enough time. Otherwise, Ibex might wake up while AES is still busy
   * and disturb the capture. Currently, we use a start trigger delay of 40
   * clock cycles and the scope captures 90 clock cycles at kClockFreqCpuHz (900
   * samples).
   */
  kIbexAesSleepCycles = 400,
};

static dif_aes_t aes;

/**
 * Simple serial 'k' (set key) command handler.
 *
 * This function does not use key shares to simplify side-channel analysis.
 * The key must be `kAesKeySize` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 * @return Result of the operation.
 */
static void aes_serial_set_key(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kAesKeyLength);
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .masking = kDifAesMaskingInternalPrng,
      .manual_operation = kDifAesManualOperationManual,
  };
  dif_aes_key_share_t key_shares;
  memcpy(key_shares.share0, key, sizeof(key_shares.share0));
  memset(key_shares.share1, 0, sizeof(key_shares.share1));
  SS_CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key_shares, NULL));
}

/**
 * Callback wrapper for AES manual trigger function.
 */
static void aes_manual_trigger(void) {
  SS_CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
}

/**
 * Encrypts a plaintext using the AES peripheral.
 *
 * This function uses `sca_call_and_sleep()` from the sca library to put Ibex to
 * sleep in order to minimize noise during captures. The plaintext must be
 * `kAesKeySize` bytes long.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 * @return Result of the operation.
 */
static void aes_serial_encrypt(const uint8_t *plaintext, size_t plaintext_len) {
  bool ready = false;
  do {
    SS_CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
  } while (!ready);
  dif_aes_data_t data;
  SS_CHECK(plaintext_len <= sizeof(data.data));
  memcpy(data.data, plaintext, plaintext_len);
  SS_CHECK_DIF_OK(dif_aes_load_data(&aes, data));

  // Start AES operation (this triggers the capture) and go to sleep.
  // Using the SecAesStartTriggerDelay hardware parameter, the AES unit is
  // configured to start operation 40 cycles after receiving the start trigger.
  // This allows Ibex to go to sleep in order to not disturb the capture.
  sca_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles);
}

/**
 * Simple serial 'p' (encrypt) command handler.
 *
 * Encrypts a `kAesKeySize` bytes long plaintext using the AES peripheral and
 * sends the ciphertext over UART. This function also handles the trigger
 * signal.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 */
static void aes_serial_single_encrypt(const uint8_t *plaintext,
                                      size_t plaintext_len) {
  SS_CHECK(plaintext_len == kAesTextLength);

  sca_set_trigger_high();
  aes_serial_encrypt(plaintext, plaintext_len);
  sca_set_trigger_low();

  bool ready = false;
  do {
    SS_CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  dif_aes_data_t ciphertext;
  SS_CHECK_DIF_OK(dif_aes_read_output(&aes, &ciphertext));
  simple_serial_send_packet('r', (uint8_t *)ciphertext.data,
                            sizeof(ciphertext.data));
}

/**
 * Simple serial 'b' (batch encrypt) command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. Instead of expecting a plaintext and sending the resulting
 * ciphertext from and to the host for each encryption, this command repeatedly
 * encrypts random plaintexts that are generated on the device. This minimizes
 * the overhead of UART communication and significantly improves the capture
 * rate. The host must use the same PRNG to be able to compute the plaintext and
 * the ciphertext of each trace.
 *
 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Since generated plaintexts are not cached, there is
 * no limit on the number of encryptions.
 *
 * The PRNG should be initialized using the 's' (seed PRNG) command before
 * starting batch encryption.
 *
 * Note that the host can partially verify this operation by checking the
 * contents of the 'r' (ciphertext) packet that is sent at the end.
 *
 * @param data Packet payload.
 * @param data_len Packet payload length.
 */
static void aes_serial_batch_encrypt(const uint8_t *data, size_t data_len) {
  uint32_t num_encryptions = 0;
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);

  sca_set_trigger_high();
  for (uint32_t i = 0; i < num_encryptions; ++i) {
    uint8_t plaintext[kAesTextLength];
    prng_rand_bytes(plaintext, kAesTextLength);
    aes_serial_encrypt(plaintext, kAesTextLength);
  }
  sca_set_trigger_low();

  bool ready = false;
  do {
    SS_CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  dif_aes_data_t ciphertext;
  SS_CHECK_DIF_OK(dif_aes_read_output(&aes, &ciphertext));
  simple_serial_send_packet('r', (uint8_t *)ciphertext.data,
                            sizeof(ciphertext.data));
}

/**
 * Initializes the AES peripheral.
 */
static void init_aes(void) {
  SS_CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  SS_CHECK_DIF_OK(dif_aes_reset(&aes));
}

/**
 * Main function.
 *
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
int main(void) {
  sca_init(kScaTriggerSourceAes, kScaPeripheralAes);

  LOG_INFO("Running AES serial");

  LOG_INFO("Initializing simple serial interface to capture board.");
  simple_serial_init(sca_get_uart());
  simple_serial_register_handler('k', aes_serial_set_key);
  simple_serial_register_handler('p', aes_serial_single_encrypt);
  simple_serial_register_handler('b', aes_serial_batch_encrypt);

  LOG_INFO("Initializing AES unit.");
  init_aes();

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}
