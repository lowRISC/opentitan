// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"
#if !OT_IS_ENGLISH_BREAKFAST
#include "sw/ip/aes/test/utils/aes_testutils.h"
#endif
#include "sw/ip/aes/dif/dif_aes.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

/**
 * OpenTitan program for AES side-channel analysis.
 *
 * This program implements the following simple serial commands:
 *   - Set key ('k')*,
 *   - Encrypt ('p')*,
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 *   - Batch encrypt ('b')*,
 *   - FvsR batch fixed key set ('f')*,
 *   - FvsR batch generate ('g')*,
 *   - FvsR batch encrypt and generate ('e')*,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library. Encryption is done in AES-ECB-128
 * mode. See https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

OTTF_DEFINE_TEST_CONFIG();

enum {
  kAesKeyLengthMax = 32,
  kAesKeyLength = 16,
  kAesTextLength = 16,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during AES operations. Caution: This number should be chosen to
   * provide enough time. Otherwise, Ibex might wake up while AES is still busy
   * and disturb the capture. Currently, we use a start trigger delay of 320
   * clock cycles and the scope captures 60 clock cycles at kClockFreqCpuHz
   * (1200 samples).
   */
  kIbexAesSleepCycles = 680,
  /**
   * Max number of encryption that can be captured with the scope
   * 81 is selected for AES with CW Husky
   * Note: Maybe it would be better if we use dynamic memory allocation but I
   * am not sure whether we are supporting it or not.
   */
  kNumBatchOpsMax = 81,
  /**
   * Max number of encryptions that can be captured before we rewrite the key to
   * reset the internal block counter. Otherwise, the AES peripheral might
   * trigger the reseeding of the internal masking PRNG which disturbs SCA
   * measurements.
   */
  kBlockCtrMax = 8191,
};

/**
 * An array of keys to be used in a batch.
 */
uint8_t batch_keys[kNumBatchOpsMax][kAesKeyLength];

/**
 * An array of plaintexts to be used in a batch.
 */
uint8_t batch_plaintexts[kNumBatchOpsMax][kAesTextLength];

/**
 * Key selection between fixed and random key during the batch capture.
 */
bool sample_fixed = true;

/**
 * Fixed key for fvsr key TVLA batch capture.
 */
uint8_t key_fixed[kAesKeyLength];

/**
 * Block counter variable for manually handling reseeding operations of the
 * masking PRNG inside the AES peripheral.
 */
static uint32_t block_ctr;

static dif_aes_t aes;

dif_aes_transaction_t transaction = {
    .operation = kDifAesOperationEncrypt,
    .mode = kDifAesModeEcb,
    .key_len = kDifAesKey128,
    .manual_operation = kDifAesManualOperationManual,
    .key_provider = kDifAesKeySoftwareProvided,
    .mask_reseeding = kDifAesReseedPer8kBlock,
    .reseed_on_key_change = false,
    .force_masks = false,
    .ctrl_aux_lock = false,
};

/**
 * Mask and configure key.
 *
 * This function masks the provided key using a software LFSR and then
 * configures the key into the AES peripheral. The masking can be disabled by
 * initializing the LFSR to 0 (see `aes_serial_seed_lfsr()`). The key must be
 * `kAesKeyLength` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 */
static void aes_key_mask_and_config(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kAesKeyLength);
  dif_aes_key_share_t key_shares;
  // Mask the provided key.
  for (int i = 0; i < key_len / 4; ++i) {
    key_shares.share1[i] =
        sca_non_linear_layer(sca_linear_layer(sca_next_lfsr(1)));
    key_shares.share0[i] = *((uint32_t *)key + i) ^ key_shares.share1[i];
  }
  // Provide random shares for unused key bits.
  for (size_t i = key_len; i < kAesKeyLengthMax / 4; ++i) {
    key_shares.share1[i] = sca_non_linear_layer(sca_next_lfsr(1));
    key_shares.share0[i] = sca_non_linear_layer(sca_next_lfsr(1));
  }
  SS_CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key_shares, NULL));
}

/**
 * Callback wrapper for AES manual trigger function.
 */
static void aes_manual_trigger(void) {
  SS_CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
}

/**
 * Simple serial 'k' (key set) command handler.
 *
 * This command is designed to set the fixed_key variable and in addition also
 * configures the key into the AES peripheral.
 *
 * The key must be `kAesKeyLength` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 */
static void aes_serial_key_set(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kAesKeyLength);
  memcpy(key_fixed, key, key_len);
  aes_key_mask_and_config(key_fixed, key_len);
  block_ctr = 0;
}

/**
 * Encrypts a plaintext using the AES peripheral.
 *
 * This function uses `sca_call_and_sleep()` from the sca library to put Ibex to
 * sleep in order to minimize noise during captures. The plaintext must be
 * `kAesTextLength` bytes long.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 */
static void aes_encrypt(const uint8_t *plaintext, size_t plaintext_len) {
  bool ready = false;
  do {
    SS_CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
  } while (!ready);

  dif_aes_data_t data;
  SS_CHECK(plaintext_len == sizeof(data.data));
  memcpy(data.data, plaintext, plaintext_len);
  SS_CHECK_DIF_OK(dif_aes_load_data(&aes, data));

  // Start AES operation (this triggers the capture) and go to sleep.
  // Using the SecAesStartTriggerDelay hardware parameter, the AES unit is
  // configured to start operation 40 cycles after receiving the start trigger.
  // This allows Ibex to go to sleep in order to not disturb the capture.
  sca_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles);
}

/**
 * Wait until AES output is valid and then get ciphertext and send it over
 * serial communication.
 *
 * @param only_first_word Send only the first word of the ciphertext.
 */
static void aes_send_ciphertext(bool only_first_word) {
  bool ready = false;
  do {
    SS_CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  dif_aes_data_t ciphertext;
  SS_CHECK_DIF_OK(dif_aes_read_output(&aes, &ciphertext));

  if (only_first_word) {
    simple_serial_send_packet('r', (uint8_t *)ciphertext.data, 4);
  } else {
    simple_serial_send_packet('r', (uint8_t *)ciphertext.data, kAesTextLength);
  }
}

/**
 * Simple serial 'p' (encrypt) command handler.
 *
 * Encrypts a `kAesTextLength` bytes long plaintext using the AES peripheral and
 * sends the ciphertext over UART. This function also handles the trigger
 * signal.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 */
static void aes_serial_single_encrypt(const uint8_t *plaintext,
                                      size_t plaintext_len) {
  SS_CHECK(plaintext_len == kAesTextLength);

  block_ctr++;
  // Rewrite the key to reset the internal block counter. Otherwise, the AES
  // peripheral might trigger the reseeding of the internal masking PRNG which
  // disturbs SCA measurements.
  if (block_ctr > kBlockCtrMax) {
    aes_key_mask_and_config(key_fixed, kAesKeyLength);
    block_ctr = 1;
  }

  sca_set_trigger_high();
  aes_encrypt(plaintext, plaintext_len);
  sca_set_trigger_low();

  aes_send_ciphertext(false);
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
 * starting batch encryption. In addition, the key should also be set
 * using 'k' (key set) command before starting batch captures.
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

  block_ctr += num_encryptions;
  // Rewrite the key to reset the internal block counter. Otherwise, the AES
  // peripheral might trigger the reseeding of the internal masking PRNG which
  // disturbs SCA measurements.
  if (block_ctr > kBlockCtrMax) {
    aes_key_mask_and_config(key_fixed, kAesKeyLength);
    block_ctr = num_encryptions;
  }

  sca_set_trigger_high();
  for (uint32_t i = 0; i < num_encryptions; ++i) {
    uint8_t plaintext[kAesTextLength];
    prng_rand_bytes(plaintext, kAesTextLength);
    aes_encrypt(plaintext, kAesTextLength);
  }
  sca_set_trigger_low();

  aes_send_ciphertext(true);
}

/**
 * Simple serial 'f' (fvsr key set) command handler.
 *
 * This command is designed to set the fixed key which is used for fvsr key TVLA
 * captures.
 *
 * The key must be `kAesKeyLength` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 */
static void aes_serial_fvsr_key_set(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kAesKeyLength);
  memcpy(key_fixed, key, key_len);
}

/**
 * Simple serial 'g' (fixed vs random key batch generate) command handler.
 *
 * This command generates random plaintexts and fixed or random keys using PRNG
 * for AES fixed vs random key batch capture in order to remove fake leakage.
 * Fixed or random key sequence is also determined here by using the lsb bit of
 * the plaintext. In order to simplify the analysis, the first encryption has to
 * use fixed key. The data collection method is based on the derived test
 * requirements (DTR) for TVLA:
 * https://www.rambus.com/wp-content/uploads/2015/08/TVLA-DTR-with-AES.pdf
 * The measurements are taken by using either fixed or randomly selected keys.
 * In addition, a PRNG is used for random key and plaintext generation instead
 * of AES algorithm as specified in the TVLA DTR.
 *
 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Number of operations of a batch should not be greater
 * than the 'kNumBatchOpsMax' value.
 *
 * The PRNG should be initialized using the 's' (seed PRNG) command before
 * starting batch captures. In addition, the fixed key should also be set
 * using 't' (fvsr key set) command before starting batch captures.
 *
 * @param data Packet payload.
 * @param data_len Packet payload length.
 */
static void aes_serial_fvsr_key_batch_generate(const uint8_t *data,
                                               size_t data_len) {
  uint32_t num_encryptions = 0;
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);
  SS_CHECK(num_encryptions <= kNumBatchOpsMax);

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    if (sample_fixed) {
      memcpy(batch_keys[i], key_fixed, kAesKeyLength);
    } else {
      prng_rand_bytes(batch_keys[i], kAesKeyLength);
    }
    // Note: To decrease memory usage, plaintexts may be generated before use in
    // every encryption operation instead of generating and storing them for all
    // encyrption operation in a batch. Also, a new method should be selected
    // to set sample_fixed variable.
    prng_rand_bytes(batch_plaintexts[i], kAesTextLength);
    sample_fixed = batch_plaintexts[i][0] & 0x1;
  }
}

/**
 * Simple serial 'e' (fixed vs random key batch encrypt and generate) command
 * handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. Instead of expecting a plaintext and sending the resulting
 * ciphertext from and to the host for each encryption, this command repeatedly
 * encrypts random plaintexts that are generated on the device. The data
 * collection method is based on the derived test requirements (DTR) for TVLA:
 * https://www.rambus.com/wp-content/uploads/2015/08/TVLA-DTR-with-AES.pdf
 * The measurements are taken by using either fixed or randomly selected keys.
 * In order to simplify the analysis, the first encryption has to use fixed key.
 * In addition, a PRNG is used for random key and plaintext generation instead
 * of AES algorithm as specified in the TVLA DTR.
 * This minimizes the overhead of UART communication and significantly improves
 * the capture rate. The host must use the same PRNG to be able to compute the
 * random plaintext, random key and the ciphertext of each trace.
 *
 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Number of operations of a batch should not be greater
 * than the 'kNumBatchOpsMax' value.
 *
 * The PRNG should be initialized using the 's' (seed PRNG) command before
 * starting batch encryption. In addition, the fixed key should also be set
 * using 't' (fvsr key set) command before starting batch encryption.
 *
 * Note that the host can partially verify this operation by checking the
 * contents of the 'r' (last ciphertext) packet that is sent at the end of every
 * batch.
 *
 * @param data Packet payload.
 * @param data_len Packet payload length.
 */
static void aes_serial_fvsr_key_batch_encrypt(const uint8_t *data,
                                              size_t data_len) {
  uint32_t num_encryptions = 0;
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);
  SS_CHECK(num_encryptions <= kNumBatchOpsMax);

  sca_set_trigger_high();
  for (uint32_t i = 0; i < num_encryptions; ++i) {
    aes_key_mask_and_config(batch_keys[i], kAesKeyLength);
    aes_encrypt(batch_plaintexts[i], kAesTextLength);
  }
  sca_set_trigger_low();

  // Only send the first word to increase capture rate
  aes_send_ciphertext(true);

  // Start to generate random keys and plaintexts for the next batch when the
  // waves are getting from scope by the host to increase capture rate.
  aes_serial_fvsr_key_batch_generate(data, data_len);
}

/**
 * Simple serial 'l' (seed lfsr) command handler.
 *
 * This function only supports 4-byte seeds.
 *
 * @param seed A buffer holding the seed.
 */
static void aes_serial_seed_lfsr(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == sizeof(uint32_t));
  sca_seed_lfsr(read_32(seed));
}

/**
 * Initializes the AES peripheral.
 */
static void init_aes(void) {
  SS_CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_DARJEELING_AES_BASE_ADDR), &aes));
  SS_CHECK_DIF_OK(dif_aes_reset(&aes));
}

/**
 * Main function.
 *
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
bool test_main(void) {
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4 | kScaPeripheralAes);

  LOG_INFO("Running AES serial");

  LOG_INFO("Initializing simple serial interface to capture board.");
  simple_serial_init(sca_get_uart());
  simple_serial_register_handler('k', aes_serial_key_set);
  simple_serial_register_handler('p', aes_serial_single_encrypt);
  simple_serial_register_handler('b', aes_serial_batch_encrypt);
  simple_serial_register_handler('f', aes_serial_fvsr_key_set);
  simple_serial_register_handler('g', aes_serial_fvsr_key_batch_generate);
  simple_serial_register_handler('e', aes_serial_fvsr_key_batch_encrypt);
  simple_serial_register_handler('l', aes_serial_seed_lfsr);

  LOG_INFO("Initializing AES unit.");
  init_aes();

#if !OT_IS_ENGLISH_BREAKFAST
  if (transaction.force_masks) {
    LOG_INFO("Initializing entropy complex.");
    CHECK_STATUS_OK(aes_testutils_masking_prng_zero_output_seed());
    CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));
  }
#endif

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}
