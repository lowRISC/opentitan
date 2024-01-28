// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/aes.h"
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
 *   - Batch encrypt alternative routine ('a')*,
 *   - Batch encrypt alternative routine, initial plaintext input ('i')*.
 *   - Set default values for AES-based data generation ('d')*,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library. Encryption is done in AES-ECB-128
 * mode. See https://wiki.newae.com/SimpleSerial for details on the protocol.
 *
 * Data for running batch capture is generated according to:
 * [DTR] Test Vector Leakage Assessment (TVLA) Derived Test Requirements (DTR)
 * with AES
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
   * clock cycles and the scope captures 60 clock cycles at kClockFreqCpuHz.
   */
  kIbexAesSleepCycles = 680,
  /**
   * The maximum number of encryptions to do per batch. The ChipWhisperer Husky
   * scope determines how many encryptions (capture segments) it wants to record
   * per batch based on the number of samples per segment. As the plaintexts
   * and keys are generated in advance for fixed-vs-random batch captures, we
   * need to make sure the corresponding buffers are sufficiently large. Note
   * that on both CW305 and CW310, the main SRAM has a size of 128 kBytes. So it
   * should be fine to allocate space for 256 segments (2 * 16 Bytes * 256 = 8
   * kBytes).
   */
  kNumBatchOpsMax = 256,
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
 * An array to store pre-computed round keys derived from the generation key.
 * The generation key (key_gen) is specified in [DTR] Section 5.1.
 * This key is used for generating all pseudo-random data for batch captures.
 * kKeyGen[kAesKeyLength] = {0x12, 0x34, 0x56, 0x78,
 *                           0x9a, 0xbc, 0xde, 0xf1,
 *                           0x23, 0x45, 0x67, 0x89,
 *                           0xab, 0xcd, 0xe0, 0xf0};
 */
static const uint32_t kKeyGenRoundKeys[(kAesKeyLength / 4) * 11] = {
    0xab239a12, 0xcd45bc34, 0xe067de56, 0xf089f178, 0xbc1734ae, 0xe12c69d5,
    0x836304da, 0x9262eb1a, 0xcb776054, 0x9d7c5039, 0x71f29195, 0x64f6947f,
    0xd2196e0e, 0x2bb6ca9a, 0xc4b547d6, 0x6602f460, 0x528099f7, 0xd1fa4c86,
    0xd317a2e5, 0x452321d5, 0x92c040d9, 0x8756ace0, 0xed3e298b, 0x92d7f4d5,
    0xfc6eaeee, 0xc84f19b5, 0x3ed3edc4, 0x2bb96e9a, 0x7a86e846, 0x99511e07,
    0x350bd835, 0xd6fd442a, 0x3c46c028, 0x47de8f91, 0x25101bc3, 0x9f49b4f0,
    0x29155393, 0xb8ff21ae, 0x36130318, 0x79e6af1b, 0xa68f9ac9, 0xcd758aab,
    0x88beadae, 0x8ef711be};

/**
 * Plaintext of the fixed set of fixed-vs-random-key TVLA
 */
static uint8_t plaintext_fixed[kAesTextLength] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa};
/**
 * Key of the of the fixed set of fixed-vs-random-key TVLA
 */
static uint8_t key_fixed[kAesTextLength] = {0x81, 0x1E, 0x37, 0x31, 0xB0, 0x12,
                                            0x0A, 0x78, 0x42, 0x78, 0x1E, 0x22,
                                            0xB2, 0x5C, 0xDD, 0xF9};
/**
 * Plaintext of the random set of fixed-vs-random-key TVLA
 */
static uint8_t plaintext_random[kAesTextLength] = {
    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc};
/**
 * Key of the random set of fixed-vs-random-key TVLA
 */
static uint8_t key_random[kAesTextLength] = {0x53, 0x53, 0x53, 0x53, 0x53, 0x53,
                                             0x53, 0x53, 0x53, 0x53, 0x53, 0x53,
                                             0x53, 0x53, 0x53, 0x53};
/**
 * Temp ciphertext variable
 */
static uint8_t ciphertext_temp[kAesTextLength];

/**
 * batch_plaintext for batch capture to initially set it using command.
 */
static uint8_t batch_plaintext[kAesTextLength];

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
    key_shares.share1[i] = sca_non_linear_layer(
        sca_linear_layer(sca_next_lfsr(1, kScaLfsrMasking)));
    key_shares.share0[i] = *((uint32_t *)key + i) ^ key_shares.share1[i];
  }
  // Provide random shares for unused key bits.
  for (size_t i = key_len; i < kAesKeyLengthMax / 4; ++i) {
    key_shares.share1[i] =
        sca_non_linear_layer(sca_next_lfsr(1, kScaLfsrMasking));
    key_shares.share0[i] =
        sca_non_linear_layer(sca_next_lfsr(1, kScaLfsrMasking));
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
 * Advances data for fvsr-key TVLA - fixed set.
 *
 * This function updates plaintext_fixed for fvsr-key TVLA, according
 * to DTR recommendations.
 */
static void aes_serial_advance_fixed(void) {
  aes_sw_encrypt_block(plaintext_fixed, kKeyGenRoundKeys, ciphertext_temp);
  memcpy(plaintext_fixed, ciphertext_temp, kAesTextLength);
}

/**
 * Advances data for fvsr-key TVLA - random set.
 *
 * This function updates plaintext_random and key_random for fvsr-key and
 * random TVLA, according to DTR recommendations.
 */
static void aes_serial_advance_random(void) {
  aes_sw_encrypt_block(plaintext_random, kKeyGenRoundKeys, ciphertext_temp);
  memcpy(plaintext_random, ciphertext_temp, kAesTextLength);
  aes_sw_encrypt_block(key_random, kKeyGenRoundKeys, ciphertext_temp);
  memcpy(key_random, ciphertext_temp, kAesTextLength);
}

/**
 * Advances data for fvsr-data TVLA - random set.
 *
 * This function updates plaintext_random for fvsr-data and
 * TVLA, according to DTR recommendations, Section 5.1.
 */
static void aes_serial_advance_random_data(void) {
  aes_sw_encrypt_block(plaintext_random, kKeyGenRoundKeys, ciphertext_temp);
  memcpy(plaintext_random, ciphertext_temp, kAesTextLength);
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
    aes_encrypt(plaintext_random, kAesTextLength);
    aes_serial_advance_random();
  }
  sca_set_trigger_low();

  aes_send_ciphertext(true);
}

/**
 * Simple serial 'a' (alternative batch encrypt) command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. It uses the first supplied plaintext and repeats AES encryptions
 * by using every ciphertext as next plaintext with a constant key. This
 * minimizes the overhead of UART communication and significantly improves the
 * capture rate.

 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Since generated plaintexts are not cached, there is
 * no limit on the number of encryptions.
 *
 * The key should also be set using 'k' (key set) command.
 *
 * The host can verify the operation by checking the last 'r' (ciphertext)
 * packet that is sent at the end.
 *
 * @param data Packet payload.
 * @param data_len Packet payload length.
 */
static void aes_serial_batch_alternative_encrypt(const uint8_t *data,
                                                 size_t data_len) {
  // Get num_encryptions from input
  uint32_t num_encryptions = 0;
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);

  // Add to current block_ctr to check if > kBlockCtrMax
  block_ctr += num_encryptions;
  // Rewrite the key to reset the internal block counter. Otherwise, the AES
  // peripheral might trigger the reseeding of the internal masking PRNG which
  // disturbs SCA measurements.
  if (block_ctr > kBlockCtrMax) {
    aes_key_mask_and_config(key_fixed, kAesKeyLength);
    block_ctr = num_encryptions;
  }

  // First plaintext has been set through command into batch_plaintext

  // Set trigger high outside of loop
  // On FPGA, the trigger is AND-ed with AES !IDLE and creates a LO-HI-LO per
  // AES operation
  sca_set_trigger_high();
  dif_aes_data_t ciphertext;
  for (uint32_t i = 0; i < num_encryptions; ++i) {
    // Encrypt
    aes_encrypt(batch_plaintext, kAesTextLength);

    // Get ciphertext
    bool ready = false;
    do {
      SS_CHECK_DIF_OK(
          dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
    } while (!ready);
    SS_CHECK_DIF_OK(dif_aes_read_output(&aes, &ciphertext));

    // Use ciphertext as next plaintext (incl. next call to this function)
    memcpy(batch_plaintext, ciphertext.data, kAesTextLength);
  }
  sca_set_trigger_low();
  // Acknowledge command
  simple_serial_send_status(0);
  // send last ciphertext
  simple_serial_send_packet('r', (uint8_t *)ciphertext.data, kAesTextLength);
}

/**
 * Simple serial 'i' (batch plaintext) command handler.
 *
 * This command is designed to set the initial plaintext for
 * aes_serial_batch_alternative_encrypt.
 *
 * The plaintext must be `kAesTextLength` bytes long.
 *
 * @param plaintext.
 * @param len.
 */
static void aes_serial_batch_plaintext_set(const uint8_t *plaintext,
                                           size_t len) {
  SS_CHECK(len == kAesTextLength);
  memcpy(batch_plaintext, plaintext, len);
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
      memcpy(batch_plaintexts[i], plaintext_fixed, kAesKeyLength);
      aes_serial_advance_fixed();
    } else {
      memcpy(batch_keys[i], key_random, kAesKeyLength);
      memcpy(batch_plaintexts[i], plaintext_random, kAesKeyLength);
      aes_serial_advance_random();
    }
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
 * This minimizes the overhead of UART communication and significantly improves
 * the capture rate.
 *
 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Number of operations of a batch should not be greater
 * than the 'kNumBatchOpsMax' value.
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

  // Acknowledge command
  simple_serial_send_status(0);

  aes_send_ciphertext(false);

  // Start to generate random keys and plaintexts for the next batch when the
  // waves are getting from scope by the host to increase capture rate.
  aes_serial_fvsr_key_batch_generate(data, data_len);
}

/**
 * Simple serial 'h' (fixed vs random data batch encrypt) command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. Instead of expecting a plaintext and sending the resulting
 * ciphertext from and to the host for each encryption, this command repeatedly
 * encrypts plaintexts that are generated on the device. The data
 * collection method is based on the derived test requirements (DTR) for TVLA:
 * https://www.rambus.com/wp-content/uploads/2015/08/TVLA-DTR-with-AES.pdf
 * The measurements are taken by using either fixed or randomly selected
 * plaintexts. In order to simplify the analysis, the first encryption has to
 * use fixed plaintext. This minimizes the overhead of UART communication and
 * significantly improves the capture rate. The host must use the same PRNG to
 * be able to compute the random plaintext and the ciphertext of each trace.
 *
 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Number of operations of a batch should not be greater
 * than the 'kNumBatchOpsMax' value.
 *
 * Note that the host can partially verify this operation by checking the
 * contents of the 'r' (last ciphertext) packet that is sent at the end of every
 * batch.
 *
 * @param data Packet payload.
 * @param data_len Packet payload length.
 */
static void aes_serial_fvsr_data_batch_encrypt(const uint8_t *data,
                                               size_t data_len) {
  uint32_t num_encryptions = 0;
  SS_CHECK(data_len == sizeof(num_encryptions));
  num_encryptions = read_32(data);
  SS_CHECK(num_encryptions <= kNumBatchOpsMax);

  for (uint32_t i = 0; i < num_encryptions; ++i) {
    // The same key is used for both fixed and random data set.
    memcpy(batch_keys[i], key_fixed, kAesKeyLength);
    if (sample_fixed) {
      memcpy(batch_plaintexts[i], plaintext_fixed, kAesKeyLength);
    } else {
      memcpy(batch_plaintexts[i], plaintext_random, kAesKeyLength);
      aes_serial_advance_random_data();
    }
    sample_fixed = sca_next_lfsr(1, kScaLfsrOrder) & 0x1;
  }

  sca_set_trigger_high();
  for (uint32_t i = 0; i < num_encryptions; ++i) {
    aes_key_mask_and_config(batch_keys[i], kAesKeyLength);
    aes_encrypt(batch_plaintexts[i], kAesTextLength);
  }
  sca_set_trigger_low();

  // Acknowledge command
  simple_serial_send_status(0);

  aes_send_ciphertext(false);
}

/**
 * Simple serial 'l' (seed lfsr) command handler.
 *
 * This function only supports 4-byte seeds.
 * Enables/disables masking depending on seed value, i.e. 0 for disable.
 *
 * @param seed A buffer holding the seed.
 */
static void aes_serial_seed_lfsr(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == sizeof(uint32_t));
  uint32_t seed_local = read_32(seed);
  if (seed_local == 0) {
    // disable masking
    transaction.force_masks = true;
  } else {
    // enable masking
    transaction.force_masks = false;
  }
  sca_seed_lfsr(seed_local, kScaLfsrMasking);
}

/**
 * Simple serial 'j' (seed lfsr) command handler.
 *
 * This function only supports 4-byte seeds.
 * Sets the seed for the LFSR used to determine the order of measurements
 * in fixed-vs-random-data dataset.
 *
 * @param seed A buffer holding the seed.
 */
static void aes_serial_seed_lfsr_order(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == sizeof(uint32_t));
  uint32_t seed_local = read_32(seed);
  sca_seed_lfsr(seed_local, kScaLfsrOrder);
}

/**
 * Simple serial 'd' (set starting values) command handler.
 *
 * This function sets starting values for FvsR data generation
 * if the received value is 1.
 * These values are specified in DTR for AES TVLA
 *
 * @param data Input command. For now only data == 1 resets values.
 */
static void aes_serial_set_default_values(const uint8_t *data,
                                          size_t data_len) {
  SS_CHECK(data_len == sizeof(uint32_t));
  uint32_t command = 0;
  command = read_32(data);
  // Starting constants for fixed-vs-random key, DTR Section 5.3
  static const uint8_t kPlaintextFixedStartFvsrKey[kAesTextLength] = {
      0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
      0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA};
  static const uint8_t kKeyFixedStartFvsrKey[kAesTextLength] = {
      0x81, 0x1E, 0x37, 0x31, 0xB0, 0x12, 0x0A, 0x78,
      0x42, 0x78, 0x1E, 0x22, 0xB2, 0x5C, 0xDD, 0xF9};
  static const uint8_t kPlaintextRandomStartFvsrKey[kAesTextLength] = {
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc};
  static const uint8_t kKeyRandomStartFvsrKey[kAesTextLength] = {
      0x53, 0x53, 0x53, 0x53, 0x53, 0x53, 0x53, 0x53,
      0x53, 0x53, 0x53, 0x53, 0x53, 0x53, 0x53, 0x53};
  // Starting constants for fixed-vs-random data, DTR Section 5.1
  static const uint8_t kPlaintextFixedStartFvsrData[kAesTextLength] = {
      0xDA, 0x39, 0xA3, 0xEE, 0x5E, 0x6B, 0x4B, 0x0D,
      0x32, 0x55, 0xBF, 0xEF, 0x95, 0x60, 0x18, 0x90};
  static const uint8_t kPlaintextRandomStartFvsrData[kAesTextLength] = {
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  static const uint8_t kKeyStartFvsrData[kAesTextLength] = {
      0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
      0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0};

  // Initial state of the prng
  static const uint32_t kPrngInitialState = 0x99999999;

  // If fixed-vs-random key analysis
  if (command == 1) {
    memcpy(plaintext_fixed, kPlaintextFixedStartFvsrKey, kAesTextLength);
    memcpy(key_fixed, kKeyFixedStartFvsrKey, kAesKeyLength);
    memcpy(plaintext_random, kPlaintextRandomStartFvsrKey, kAesTextLength);
    memcpy(key_random, kKeyRandomStartFvsrKey, kAesKeyLength);
  }

  // If fixed-vs-random data analysis
  if (command == 2) {
    memcpy(plaintext_fixed, kPlaintextFixedStartFvsrData, kAesTextLength);
    memcpy(key_fixed, kKeyStartFvsrData, kAesKeyLength);
    memcpy(plaintext_random, kPlaintextRandomStartFvsrData, kAesTextLength);
  }

  sca_seed_lfsr(kPrngInitialState, kScaLfsrOrder);
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
  simple_serial_register_handler('h', aes_serial_fvsr_data_batch_encrypt);
  simple_serial_register_handler('l', aes_serial_seed_lfsr);
  simple_serial_register_handler('j', aes_serial_seed_lfsr_order);
  simple_serial_register_handler('a', aes_serial_batch_alternative_encrypt);
  simple_serial_register_handler('i', aes_serial_batch_plaintext_set);
  simple_serial_register_handler('d', aes_serial_set_default_values);

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
