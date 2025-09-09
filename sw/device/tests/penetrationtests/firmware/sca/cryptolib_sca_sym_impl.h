// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_IMPL_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_sym_commands.h"

/**
 * Wrapper to AES cryptolib implementation.
 *
 * @param data_in Input data.
 * @param data_in_len Input data length.
 * @param key Key.
 * @param key_len  Key length.
 * @param iv IV.
 * @param data_out Output data.
 * @param data_out_len Output data length.
 * @param padding Padding.
 * @param mode Mode.
 * @param op_enc Encryption or decryption.
 * @param cfg_in Input config.
 * @param cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_aes_impl(uint8_t data_in[AES_CMD_MAX_MSG_BYTES],
                                size_t data_in_len,
                                uint8_t key[AES_CMD_MAX_KEY_BYTES],
                                size_t key_len,
                                uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
                                uint8_t data_out[AES_CMD_MAX_MSG_BYTES],
                                size_t *data_out_len, size_t padding,
                                size_t mode, bool op_enc, size_t cfg_in,
                                size_t *cfg_out, size_t trigger);

/**
 * Wrapper to DRBG generate cryptolib implementation.
 *
 * @param nonce Used in the generate command of DRBG.
 * @param nonce_len  Length in bytes.
 * @param[out] data_out Generated data.
 * @param data_out_len Length in bytes.
 * @param reseed_interval Intervall when a reseed is triggered.
 * @param mode Mode.
 * @param cfg_in Input config.
 * @param cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_drbg_generate_impl(
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    uint8_t data_out[DRBG_CMD_MAX_OUTPUT_BYTES], size_t data_out_len,
    size_t mode, size_t cfg_in, size_t *cfg_out, size_t trigger);

/**
 * Wrapper to DRBG reseed/instantiate cryptolib implementation.
 *
 * @param entropy Used in the instantiation of DRBG.
 * @param entropy_len Length in bytes.
 * @param nonce Used in the generate command of DRBG.
 * @param nonce_len  Length in bytes.
 * @param reseed_interval Intervall when a reseed is triggered.
 * @param mode Mode.
 * @param cfg_in Input config.
 * @param cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_drbg_reseed_impl(
    uint8_t entropy[DRBG_CMD_MAX_ENTROPY_BYTES], size_t entropy_len,
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    size_t reseed_interval, size_t mode, size_t cfg_in, size_t *cfg_out,
    size_t trigger);

/**
 * Wrapper to AES-GCM cryptolib implementation.
 *
 * @param data_in .
 * @param data_in_len .
 * @param aad .
 * @param aad_len .
 * @param key .
 * @param key_len .
 * @param iv .
 * @param[out] data_out .
 * @param[out] data_out_len .
 * @param[out] tag .
 * @param[out] tag_len .
 * @param cfg_in .
 * @param[out] cfg_out .
 * @param trigger .
 * @return OK or error.
 */
status_t cryptolib_sca_gcm_impl(
    uint8_t data_in[AES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t aad[AES_CMD_MAX_MSG_BYTES], size_t aad_len,
    uint8_t key[AES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[AES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    uint8_t tag[AES_CMD_MAX_MSG_BYTES], size_t *tag_len, size_t cfg_in,
    size_t *cfg_out, size_t trigger);

/**
 * Wrapper to HMAC cryptolib implementation.
 *
 * @param data_in Input data.
 * @param data_in_len Input data length.
 * @param key Key.
 * @param key_len  Key length.
 * @param data_out Output data.
 * @param data_out_len Output data length.
 * @param mode Mode.
 * @param cfg_in Input config.
 * @param cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_hmac_impl(uint8_t data_in[HMAC_CMD_MAX_MSG_BYTES],
                                 size_t data_in_len,
                                 uint8_t key[HMAC_CMD_MAX_KEY_BYTES],
                                 size_t key_len,
                                 uint8_t data_out[HMAC_CMD_MAX_TAG_BYTES],
                                 size_t *data_out_len, size_t hash_mode,
                                 size_t mode, size_t cfg_in, size_t *cfg_out,
                                 size_t trigger);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_IMPL_H_
