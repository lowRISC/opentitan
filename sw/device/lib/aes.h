// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_AES_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// TODO:
// 1) Refactor to use use dif_aes.
// 2) Verify that test still works.
// 3) Use dif_aes directly in the test (probably remove this file).

/**
 * Supported AES operation modes: encode or decode.
 */
typedef enum aes_op { kAesEnc = 0, kAesDec = 1 } aes_op_t;

/**
 * Supported AES block cipher modes: ECB, CBC, CTR. The hardware uses a one-hot
 * encoding. NONE is not a supported mode but the reset value of the hardware.
 * The hardware resolves invalid mode values to NONE.
 */
typedef enum aes_mode {
  kAesEcb = 1 << 0,
  kAesCbc = 1 << 1,
  kAesCtr = 1 << 2,
  kAesNone = 1 << 3
} aes_mode_t;

/**
 * Supported AES key lengths: 128 bit, 192 bit or 256 bit. The hardware uses a
 * one-hot encoding.
 */
typedef enum aes_key_len {
  kAes128 = 1 << 0,
  kAes192 = 1 << 1,
  kAes256 = 1 << 2
} aes_key_len_t;

/**
 * AES unit configuration options.
 */
typedef struct aes_cfg {
  /** Operational mode @see aes_op. */
  aes_op_t operation;
  /** Block cipher mode @see aes_mode. */
  aes_mode_t mode;
  /** Key length @see aes_key_len. */
  aes_key_len_t key_len;
  /** Set to 1 to i) only start upon getting a trigger signal, and ii) not stall
   * when previous output data has not been read. */
  bool manual_operation;
} aes_cfg_t;

/**
 * Intialize AES unit to desired mode.
 *
 * @param aes_cfg AES configuration settings.
 */
void aes_init(aes_cfg_t aes_cfg);

/**
 * Pass initial encryption key to AES unit.
 *
 * @param key_share0 pointer to key share 0.
 * @param key_share1 pointer to key share 1.
 * @param key_len    key length, given as a enum value.
 */
void aes_key_put(const void *key_share0, const void *key_share1,
                 aes_key_len_t key_len);

/**
 * Wait for AES unit to be ready for new input data and then
 * pass one 16B block of input data to AES unit.
 *
 * @param data pointer to input buffer.
 */
void aes_data_put_wait(const void *data);

/**
 * Pass one 16B block of input data to AES unit.
 *
 * @param data pointer to input buffer.
 */
void aes_data_put(const void *data);

/**
 * Wait for AES unit to have valid output data and then
 * get one 16B block of output data from AES unit.
 *
 * @param[out] data pointer to output buffer.
 */
void aes_data_get_wait(void *data);

/**
 * Get one 16B block of output data from AES unit.
 *
 * @param[out] data pointer to output buffer.
 */
void aes_data_get(void *data);

/**
 * Check AES unit for being ready to accept new input data.
 *
 * @return true if ready for new input data, false otherwise.
 */
bool aes_data_ready(void);

/**
 * Check AES unit for having valid output data.
 *
 * @return true if valid output data available, false otherwise.
 */
bool aes_data_valid(void);

/**
 * Check AES unit for being idle.
 *
 * @return true if idle, false otherwise.
 */
bool aes_idle(void);

/**
 * Set AES manual trigger.
 *
 * This is only valid when AES is configured to run in manual mode.
 */
void aes_manual_trigger(void);

/**
 * Clear key, input and ouput registers of AES unit.
 */
void aes_clear(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_AES_H_
