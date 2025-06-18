// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * cryptolib aes sca fvsr plaintext test
 *
 * This SCA penetration test triggers num_iterations cryptolib AES operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_aes_fvsr_plaintext(ujson_t *uj);

/**
 * cryptolib aes sca fvsr key test
 *
 * This SCA penetration test triggers num_iterations cryptolib AES operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_aes_fvsr_key(ujson_t *uj);

/**
 * cryptolib cmac sca fvsr plaintext test
 *
 * This SCA penetration test triggers num_iterations cryptolib CMAC operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_cmac_fvsr_plaintext(ujson_t *uj);

/**
 * cryptolib cmac sca fvsr key test
 *
 * This SCA penetration test triggers num_iterations cryptolib CMAC operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_cmac_fvsr_key(ujson_t *uj);

/**
 * cryptolib gcm sca fvsr plaintext test
 *
 * This SCA penetration test triggers num_iterations cryptolib GCM operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_gcm_fvsr_plaintext(ujson_t *uj);

/**
 * cryptolib gcm sca fvsr key test
 *
 * This SCA penetration test triggers num_iterations cryptolib GCM operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_gcm_fvsr_key(ujson_t *uj);

/**
 * cryptolib tdes sca fvsr plaintext test
 *
 * This SCA penetration test triggers num_iterations cryptolib TDES operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_tdes_fvsr_plaintext(ujson_t *uj);

/**
 * cryptolib tdes sca fvsr key test
 *
 * This SCA penetration test triggers num_iterations cryptolib TDES operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_tdes_fvsr_key(ujson_t *uj);

/**
 * cryptolib hmac sca fvsr plaintext test
 *
 * This SCA penetration test triggers num_iterations cryptolib HMAC operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_hmac_fvsr_plaintext(ujson_t *uj);

/**
 * cryptolib hmac sca fvsr key test
 *
 * This SCA penetration test triggers num_iterations cryptolib HMAC operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_hmac_fvsr_key(ujson_t *uj);

/**
 * cryptolib drbg sca fvsr test
 *
 * This SCA penetration test triggers num_iterations cryptolib DRBG operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_drbg_fvsr(ujson_t *uj);

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
status_t handle_cryptolib_sca_rsa_dec(ujson_t *uj);

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
status_t handle_cryptolib_sca_rsa_sign(ujson_t *uj);

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
status_t handle_cryptolib_sca_prime(ujson_t *uj);

/**
 * The cryptolib sca p256 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p256_base_mul(ujson_t *uj);

/**
 * The cryptolib sca p256 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p256_point_mul(ujson_t *uj);

/**
 * The cryptolib sca p256 sign handler.
 *
 * This SCA penetration test triggers a sign on p256.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p256_sign(ujson_t *uj);

/**
 * The cryptolib sca p384 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p384_base_mul(ujson_t *uj);

/**
 * The cryptolib sca p384 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p384_point_mul(ujson_t *uj);

/**
 * The cryptolib sca p384 sign handler.
 *
 * This SCA penetration test triggers a sign on p384.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_p384_sign(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_secp256k1_base_mul(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_secp256k1_point_mul(ujson_t *uj);

/**
 * The cryptolib sca secp256k1 sign handler.
 *
 * This SCA penetration test triggers a sign on secp256k1.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_secp256k1_sign(ujson_t *uj);

/**
 * The cryptolib sca x25519 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_x25519_base_mul(ujson_t *uj);

/**
 * The cryptolib sca x25519 point mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and a
 * chosen point. It takes two scalars, the Bob scalar is multiplied by the base
 * point and then multiplied by Alice's scalar.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_x25519_point_mul(ujson_t *uj);

/**
 * The cryptolib sca ed25519 base mul handler.
 *
 * This SCA penetration test triggers a multiplication between a scalar and the
 * base point.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_ed25519_base_mul(ujson_t *uj);

/**
 * The cryptolib sca ed25519 sign handler.
 *
 * This SCA penetration test triggers a sign on ed25519.
 *
 * See cryptolib_sca_commands.h for inputs and outputs.
 * See sca_cryptolib.json for examples of its use.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_ed25519_sign(ujson_t *uj);

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib SCA firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_init(ujson_t *uj);

/**
 * CryptoLib SCA command handler.
 *
 * Command handler for the CryptoLib SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_H_
