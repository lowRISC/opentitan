// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_AES_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * Supported AES modes: encode or decode.
 */
typedef enum aes_mode { kAesEnc = 0, kAesDec = 1 } aes_mode_t;

/**
 * Supported AES key lengths: 128 bit, 192 bit or 256 bit. The hardware uses a
 * one-hot encoding.
 */
typedef enum aes_key_len {
  kAes128 = 0x1,
  kAes192 = 0x2,
  kAes256 = 0x4
} aes_key_len_t;

/**
 * AES unit configuration options.
 */
typedef struct aes_cfg {
  /** Operational mode @see aes_mode. */
  aes_mode_t mode;
  /** Key length @see aes_key_len. */
  aes_key_len_t key_len;
  /** Set to 1 to only start upon getting a trigger signal. */
  bool manual_start_trigger;
  /** Set to 1 to not stall when previous output data has not been read. */
  bool force_data_overwrite;
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
 * @param key     pointer to key.
 * @param key_len key length, given as a enum value.
 */
void aes_key_put(const void *key, aes_key_len_t key_len);

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
 * @param data pointer to output buffer.
 */
void aes_data_get_wait(void *data);

/**
 * Get one 16B block of output data from AES unit.
 *
 * @param data pointer to output buffer.
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
 * Clear key, input and ouput registers of AES unit.
 */
void aes_clear(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_AES_H_
