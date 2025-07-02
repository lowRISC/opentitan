// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The cryptolib fi rsa enc handler.
 *
 * This command encrypts or decrypts using an RSA call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_rsa_enc(ujson_t *uj);

/**
 * The cryptolib fi rsa sign handler.
 *
 * This command signs using an RSA call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_rsa_sign(ujson_t *uj);

/**
 * The cryptolib fi rsa verify handler.
 *
 * This command verifies using an RSA call accepting multiple
 * padding schemes and modes of operation.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_rsa_verify(ujson_t *uj);

/**
 * The cryptolib fi drbg handler.
 *
 * This command generates a prime.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_prime(ujson_t *uj);

/**
 * The cryptolib fi p256 base mul handler.
 *
 * This command performs a multiplication between a scalar and the base point.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p256_base_mul(ujson_t *uj);

/**
 * The cryptolib fi p256 point mul handler.
 *
 * This command performs a multiplication between a scalar and a chosen point.
 * It takes two scalars, the Bob scalar is multiplied by the base point and then
 * multiplied by Alice's scalar.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p256_point_mul(ujson_t *uj);

/**
 * The cryptolib fi p256 sign handler.
 *
 * This command signs on p256.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p256_sign(ujson_t *uj);

/**
 * The cryptolib fi p256 verify handler.
 *
 * This command verifies a signature for p256.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p256_verify(ujson_t *uj);

/**
 * The cryptolib fi p384 base mul handler.
 *
 * This command performs a multiplication between a scalar and the base point.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p384_base_mul(ujson_t *uj);

/**
 * The cryptolib fi p384 point mul handler.
 *
 * This command performs a multiplication between a scalar and a chosen point.
 * It takes two scalars, the Bob scalar is multiplied by the base point and then
 * multiplied by Alice's scalar.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p384_point_mul(ujson_t *uj);

/**
 * The cryptolib fi p384 sign handler.
 *
 * This command signs on p384.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p384_sign(ujson_t *uj);

/**
 * The cryptolib fi p384 verify handler.
 *
 * This command verifies a signature for p384.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_p384_verify(ujson_t *uj);

/**
 * The cryptolib fi secp256k1 base mul handler.
 *
 * This command performs a multiplication between a scalar and the base point.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_secp256k1_base_mul(ujson_t *uj);

/**
 * The cryptolib fi secp256k1 point mul handler.
 *
 * This command performs a multiplication between a scalar and a chosen point.
 * It takes two scalars, the Bob scalar is multiplied by the base point and then
 * multiplied by Alice's scalar.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_secp256k1_point_mul(ujson_t *uj);

/**
 * The cryptolib fi secp256k1 sign handler.
 *
 * This command signs on secp256k1.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_secp256k1_sign(ujson_t *uj);

/**
 * The cryptolib fi secp256k1 verify handler.
 *
 * This command verifies a signature for secp256k1.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_secp256k1_verify(ujson_t *uj);

/**
 * The cryptolib fi x25519 base mul handler.
 *
 * This command performs a multiplication between a scalar and the base point.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_x25519_base_mul(ujson_t *uj);

/**
 * The cryptolib fi x25519 point mul handler.
 *
 * This command performs a multiplication between a scalar and a chosen point.
 * It takes two scalars, the Bob scalar is multiplied by the base point and then
 * multiplied by Alice's scalar.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_x25519_point_mul(ujson_t *uj);

/**
 * The cryptolib fi ed25519 base mul handler.
 *
 * This command performs a multiplication between a scalar and the base point.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_ed25519_base_mul(ujson_t *uj);

/**
 * The cryptolib fi ed25519 sign handler.
 *
 * This command signs on ed25519.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_ed25519_sign(ujson_t *uj);

/**
 * The cryptolib fi ed25519 verify handler.
 *
 * This command verifies a signature for ed25519.
 *
 * See cryptolib_fi_asym_commands.h for inputs and outputs.
 * See fi_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_ed25519_verify(ujson_t *uj);

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib FI firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym_init(ujson_t *uj);

/**
 * CryptoLib FI command handler.
 *
 * Command handler for the CryptoLib FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_asym(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_H_
