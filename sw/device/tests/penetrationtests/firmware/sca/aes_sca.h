// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The result of an AES SCA operation.
 */
typedef enum aes_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  aesScaOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  aesScaAborted = 1,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that would go out of range.
   */
  aesScaOutOfRange = 2
} aes_sca_error_t;

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
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_alternative_encrypt(ujson_t *uj);

/**
 * Batch encrypt command handler.
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
 * The PRNG should be initialized using the seed PRNG command before
 * starting batch encryption. In addition, the key should also be set
 * using key set command before starting batch captures.
 *
 * Note that the host can partially verify this operation by checking the
 * contents of UART reponse that is sent at the end.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_encrypt(ujson_t *uj);

/**
 * Batch encrypt random command handler.
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
 * The PRNG should be initialized using the seed PRNG command before
 * starting batch encryption. In addition, the key should also be set
 * using key set command before starting batch captures.
 *
 * Note that the host can partially verify this operation by checking the
 * contents of UART reponse that is sent at the end.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_encrypt_random(ujson_t *uj);

/**
 * Batch plaintext command handler.
 *
 * This command is designed to set the initial plaintext for
 * aes_serial_batch_alternative_encrypt.
 *
 * The plaintext must be `kAesTextLength` bytes long.
 *
 *  * The uJSON data contains:
 *  - text: The plaintext.
 *  - text_length: Plaintext length.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_plaintext_set(ujson_t *uj);

/**
 * Fixed vs random data batch encrypt and generate command handler.
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
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_fvsr_data_batch_encrypt(ujson_t *uj);

/**
 * Fixed vs random key batch encrypt and generate command handler.
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
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_fvsr_key_batch_encrypt(ujson_t *uj);

/**
 * Fixed vs random key batch generate command handler.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_fvsr_key_batch_generate(ujson_t *uj);

/**
 * Fvsr key set command handler.
 *
 * This command is designed to set the fixed key which is used for fvsr key TVLA
 * captures.
 *
 * The key must be `kAesKeyLength` bytes long.
 *
 * The uJSON data contains:
 *  - key: The key to use.
 *  - key_length: The length of the key.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_fvsr_key_set(ujson_t *uj);

/**
 * Set starting values command handler.
 *
 * This function sets starting values for FvsR data generation
 * if the received value is 1.
 * These values are specified in DTR for AES TVLA.
 *
 * The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_fvsr_key_start_batch_generate(ujson_t *uj);

/**
 * Initialize AES command handler.
 *
 * This command is designed to setup the AES.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_pentest_init(ujson_t *uj);

/**
 * Key set command handler.
 *
 * This command is designed to set the fixed_key variable and in addition also
 * configures the key into the AES peripheral.
 *
 * The key must be `kAesKeyLength` bytes long.
 *
 * The uJSON data contains:
 *  - key: The key to use.
 *  - key_length: The length of the key.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_key_set(ujson_t *uj);

/**
 * Seed lfsr command handler.
 *
 * This function only supports 4-byte seeds.
 * Enables/disables masking depending on seed value, i.e. 0 for disable.
 *
 * The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_pentest_seed_lfsr(ujson_t *uj);

/**
 * Seed lfsr command handler.
 *
 * This function only supports 4-byte seeds.
 * Sets the seed for the LFSR used to determine the order of measurements
 * in fixed-vs-random-data dataset.
 *
 * The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_pentest_seed_lfsr_order(ujson_t *uj);

/**
 * Single encrypt command handler.
 *
 * Encrypts a `kAesTextLength` bytes long plaintext using the AES peripheral and
 * sends the ciphertext over UART. This function also handles the trigger
 * signal.
 *
 * The uJSON data contains:
 *  - text: The plaintext.
 *  - text_length: The length of the plaintext.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_single_encrypt(ujson_t *uj);

/**
 * HMAC SCA command handler.
 *
 * Command handler for the HMAC SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_
