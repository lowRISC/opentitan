// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The cryptolib fi aes handler.
 *
 * This command encrypts or decrypts using an AES call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_aes(ujson_t *uj);

/**
 * The cryptolib fi cmac handler.
 *
 * This command generates and verifies a tag using CMAC.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_cmac(ujson_t *uj);

/**
 * The cryptolib fi gcm handler.
 *
 * This command generates a ciphertext and a tag which is verified using GCM.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_gcm(ujson_t *uj);

/**
 * The cryptolib fi tdes handler.
 *
 * This command encrypts or decrypts using a TDES call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_tdes(ujson_t *uj);

/**
 * The cryptolib fi hmac handler.
 *
 * This command uses an HMAC call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_hmac(ujson_t *uj);

/**
 * The cryptolib fi drbg generate handler.
 *
 * This command generates randomness using a DRBG call.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_drbg_generate(ujson_t *uj);

/**
 * The cryptolib fi drbg reseed handler.
 *
 * This command reseeds/instantiates the DRBG call.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_drbg_reseed(ujson_t *uj);

/**
 * The cryptolib fi trng generate handler.
 *
 * This command generates randomness from the trng.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_trng_generate(ujson_t *uj);

/**
 * The cryptolib fi trng init handler.
 *
 * This command instantiates the TRNG.
 *
 * See cryptolib_fi_sym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_trng_init(ujson_t *uj);

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib FI firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym_init(ujson_t *uj);

/**
 * CryptoLib FI command handler.
 *
 * Command handler for the CryptoLib FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_sym(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_SYM_H_
