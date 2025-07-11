// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * cryptolib rsa sca dec test
 *
 * This SCA penetration test triggers a cryptolib RSA decrypt operation.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_rsa_dec_fvsr(ujson_t *uj);

/**
 * cryptolib rsa sca dec test with daisy chaining
 *
 * This SCA penetration test triggers a cryptolib RSA decrypt operation.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_rsa_dec_daisy_chain(ujson_t *uj);

/**
 * cryptolib rsa sca sign test
 *
 * This SCA penetration test triggers a cryptolib RSA sign operation.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_rsa_sign_fvsr(ujson_t *uj);

/**
 * cryptolib rsa sca sign test with daisy chaining
 *
 * This SCA penetration test triggers a cryptolib RSA sign operation.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_rsa_sign_daisy_chain(ujson_t *uj);

/**
 * cryptolib rsa sca dec test
 *
 * This SCA penetration test triggers a prime generation.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_prime(ujson_t *uj);

/**
 * The cryptolib sca p256 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p256_base_mul_fsvr(ujson_t *uj);

/**
 * The cryptolib sca p256 base mul handler with daisy chaining.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p256_base_mul_daisy_chain(ujson_t *uj);

/**
 * The cryptolib sca p256 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p256_point_mul(ujson_t *uj);

/**
 * The cryptolib sca p256 ecdh handler.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p256_ecdh(ujson_t *uj);

/**
 * The cryptolib sca p256 sign handler.
 *
 * This SCA penetration test triggers a sign on p256.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p256_sign(ujson_t *uj);

/**
 * The cryptolib sca p384 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p384_base_mul_fvsr(ujson_t *uj);

/**
 * The cryptolib sca p384 base mul handler with daisy chaining.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p384_base_mul_daisy_chain(ujson_t *uj);

/**
 * The cryptolib sca p384 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p384_point_mul(ujson_t *uj);

/**
 * The cryptolib sca p384 ecdh handler.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p384_ecdh(ujson_t *uj);

/**
 * The cryptolib sca p384 sign handler.
 *
 * This SCA penetration test triggers a sign on p384.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_p384_sign(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_secp256k1_base_mul_fvsr(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 base mul handler with daisy chaining.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_secp256k1_base_mul_daisy_chaining(
    ujson_t *uj);

/**
 * The cryptolib sca secp256k1 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_secp256k1_point_mul(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 ecdh handler.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_secp256k1_ecdh(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 sign handler.
 *
 * This SCA penetration test triggers a sign on secp256k1.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_secp256k1_sign(ujson_t *uj);

/**
 * The cryptolib sca x25519 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_x25519_base_mul_fvsr(ujson_t *uj);

/**
 * The cryptolib sca x25519 base mul handler with daisy chaining.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_x25519_base_mul_daisy_chaining(ujson_t *uj);

/**
 * The cryptolib sca x25519 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_x25519_point_mul(ujson_t *uj);

/**
 * The cryptolib sca x25519 ecdh handler.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_x25519_ecdh(ujson_t *uj);

/**
 * The cryptolib sca ed25519 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_ed25519_base_mul_fsvr(ujson_t *uj);

/**
 * The cryptolib sca ed25519 base mul handler with daisy chaining.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_ed25519_base_mul_daisy_chaining(ujson_t *uj);

/**
 * The cryptolib sca ed25519 sign handler.
 *
 * This SCA penetration test triggers a sign on ed25519.
 *
 * See cryptolib_sca_asymcommands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_ed25519_sign(ujson_t *uj);

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib SCA firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym_init(ujson_t *uj);

/**
 * CryptoLib SCA command handler.
 *
 * Command handler for the CryptoLib SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_asym(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_ASYM_H_
