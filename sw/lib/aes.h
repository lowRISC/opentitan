// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_LIB_AES_H__
#define _F_LIB_AES_H__

#include <stddef.h>
#include <stdint.h>

/**
 * Supported AES modes
 */
typedef enum aes_modes { AES_ENC = 0, AES_DEC = 1 } aes_modes_t;

/**
 * AES unit configuration options.
 */
typedef struct hmac_cfg {
  /** Operational mode @see aes_modes. */
  aes_modes_t mode;
  /** Can be 16, 24 or 32. */
  size_t key_len_in_bytes;
  /** Set to 1 to only start upon getting a trigger signal. */
  unsigned char manual_start_trigger;
  /** Set to 1 to not stall when previous output data has not been read. */
  unsigned char force_data_overwrite;
} aes_cfg_t;

/**
 * Intialize AES unit to desired mode.
 *
 * @param aes_cfg AES configuration settings.
 */
void aes_init(const aes_cfg_t aes_cfg);

/**
 * Pass initial encryption key to AES unit.
 *
 * @param key              pointer to key.
 * @param key_len_in_bytes key length in bytes (16, 24, 32)
 */
void aes_key_put(const void *key, const size_t key_len_in_bytes);

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
 * Poll for AES unit being ready to accept new input data.
 */
void aes_data_ready(void);

/**
 * Poll for AES unit having valid output data.
 */
void aes_data_valid(void);

/**
 * Poll for AES unit being idle.
 */
void aes_idle(void);

/**
 * Clear key, input and ouput registers of AES unit.
 */
void aes_clear(void);

#endif  // _F_LIB_AES_H__
