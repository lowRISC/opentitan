// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_IMPL_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_sym_commands.h"

/**
 * Wrapper to AES cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_aes_impl(cryptolib_fi_sym_aes_in_t uj_input,
                               cryptolib_fi_sym_aes_out_t *uj_output);

/**
 * Wrapper to DRBG generate cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_drbg_generate_impl(
    cryptolib_fi_sym_drbg_generate_in_t uj_input,
    cryptolib_fi_sym_drbg_generate_out_t *uj_output);

/**
 * Wrapper to DRBG reseed/instantiate cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_drbg_reseed_impl(
    cryptolib_fi_sym_drbg_reseed_in_t uj_input,
    cryptolib_fi_sym_drbg_reseed_out_t *uj_output);

/**
 * Wrapper to AES-GCM cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_gcm_impl(cryptolib_fi_sym_gcm_in_t uj_input,
                               cryptolib_fi_sym_gcm_out_t *uj_output);

/**
 * Wrapper to HMAC cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_hmac_impl(cryptolib_fi_sym_hmac_in_t uj_input,
                                cryptolib_fi_sym_hmac_out_t *uj_output);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_IMPL_H_
