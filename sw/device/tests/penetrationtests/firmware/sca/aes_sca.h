// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

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
 * This command is designed to maximize the capture rate for side-channel
 * attacks. It uses the first supplied plaintext and repeats AES encryptions
 * by using every ciphertext as next plaintext with a constant key. This
 * minimizes the overhead of UART communication and significantly improves the
 * capture rate.

 * Packet payload must be a `uint32_t` representation of the number of
 * encryptions to perform. Since generated plaintexts are not cached, there is
 * no limit on the number of encryptions.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_daisy_chain(ujson_t *uj);

/**
 * Batch random command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. Instead of expecting a plaintext and sending the resulting
 * ciphertext from and to the host for each encryption, this command repeatedly
 * encrypts random plaintexts that are generated on the device. This minimizes
 * the overhead of UART communication and significantly improves the capture
 * rate. The host must use the same PRNG to be able to compute the plaintext and
 * the ciphertext of each trace.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_random(ujson_t *uj);

/**
 * Batch fvsr data command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. This command coins randomness to decide whether to encrypt the given
 * plaintext or a random one. This minimizes the overhead of UART communication
 * and significantly improves the capture rate. The host must use the same PRNG
 * to be able to compute the plaintext and the ciphertext of each trace.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_fvsr_data(ujson_t *uj);

/**
 * Batch fvsr key command handler.
 *
 * This command is designed to maximize the capture rate for side-channel
 * attacks. This command coins randomness to decide whether to encrypt a random
 * plaintext with the given key or a random key. This minimizes the overhead of
 * UART communication and significantly improves the capture rate. The host must
 * use the same PRNG to be able to compute the plaintext and the ciphertext of
 * each trace.
 *
 * The uJSON data contains:
 *  - data: The number of encryptions.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_batch_fvsr_key(ujson_t *uj);

/**
 * Invokes an AES-GCM encryption with tag generation.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca_gcm_single_encrypt(ujson_t *uj);

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
 * HMAC SCA command handler.
 *
 * Command handler for the HMAC SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_aes_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_AES_SCA_H_
