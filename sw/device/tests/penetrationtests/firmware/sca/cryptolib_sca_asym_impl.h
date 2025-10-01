// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_IMPL_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_asym_commands.h"

/**
 * Wrapper to RSA decryption implementation.
 *
 * @param data Input data.
 * @param data_len Input data length.
 * @param mode Mode.
 * @param n RSA modulus.
 * @param d RSA private key.
 * @param[out] n_len RSA length.
 * @param[out] data_out Output data.
 * @param[out] data_out_len Output data length.
 * @param hashing Hashing mode.
 * @param padding Padding mode.
 * @param cfg_in Input config.
 * @param[out] cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_rsa_dec_impl(
    uint8_t data[RSA_CMD_MAX_MESSAGE_BYTES], size_t data_len, size_t mode,
    uint8_t n[RSA_CMD_MAX_N_BYTES], uint8_t d[RSA_CMD_MAX_N_BYTES],
    size_t *n_len, uint8_t data_out[RSA_CMD_MAX_MESSAGE_BYTES],
    size_t *data_out_len, size_t hashing, size_t padding, size_t cfg_in,
    size_t *cfg_out, size_t trigger);

/**
 * Wrapper to RSA decryption implementation.
 *
 * @param data Input data.
 * @param data_len Input data length.
 * @param n RSA modulus.
 * @param d RSA private key.
 * @param[out] n_len RSA length.
 * @param[out] sig Output data.
 * @param[out] sig_len Output data length.
 * @param hashing Hashing mode.
 * @param padding Padding mode.
 * @param cfg_in Input config.
 * @param[out] cfg_out Output config.
 * @param trigger Trigger config.
 * @return OK or error.
 */
status_t cryptolib_sca_rsa_sign_impl(
    uint8_t data[RSA_CMD_MAX_MESSAGE_BYTES], size_t data_len,
    uint8_t n[RSA_CMD_MAX_N_BYTES], uint8_t d[RSA_CMD_MAX_N_BYTES],
    size_t *n_len, uint8_t sig[RSA_CMD_MAX_SIGNATURE_BYTES], size_t *sig_len,
    size_t hashing, size_t padding, size_t cfg_in, size_t *cfg_out,
    size_t trigger);

/**
 * Wrapper to ECDH in P256 cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_sca_p256_ecdh_impl(
    cryptolib_sca_asym_p256_ecdh_in_t uj_input,
    cryptolib_sca_asym_p256_ecdh_out_t *uj_output);

/**
 * Wrapper to P256 Sign cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_sca_p256_sign_impl(
    cryptolib_sca_asym_p256_sign_in_t uj_input,
    cryptolib_sca_asym_p256_sign_out_t *uj_output);

/**
 * Wrapper to ECDH in P384 cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_sca_p384_ecdh_impl(
    cryptolib_sca_asym_p384_ecdh_in_t uj_input,
    cryptolib_sca_asym_p384_ecdh_out_t *uj_output);

/**
 * Wrapper to P384 Sign cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_sca_p384_sign_impl(
    cryptolib_sca_asym_p384_sign_in_t uj_input,
    cryptolib_sca_asym_p384_sign_out_t *uj_output);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_IMPL_H_
