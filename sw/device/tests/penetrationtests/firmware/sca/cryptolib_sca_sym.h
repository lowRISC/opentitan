// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_H_

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
status_t handle_cryptolib_sca_sym_aes_fvsr_plaintext(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_aes_fvsr_key(ujson_t *uj);

/**
 * cryptolib aes sca daisy chain test
 *
 * This SCA penetration test triggers num_iterations cryptolib AES operations
 * using daisy chaining meaning that the output is copied to the input.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_aes_daisy_chain(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_cmac_fvsr_plaintext(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_cmac_fvsr_key(ujson_t *uj);

/**
 * cryptolib cmac sca daisy chain test
 *
 * This SCA penetration test triggers num_iterations cryptolib CMAC operations
 * using daisy chaining meaning that the output is copied to the input.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_cmac_daisy_chain(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_gcm_fvsr_plaintext(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_gcm_fvsr_key(ujson_t *uj);

/**
 * cryptolib gcm sca daisy chain test
 *
 * This SCA penetration test triggers num_iterations cryptolib GCM operations
 * using daisy chaining meaning that the output is copied to the input.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_gcm_daisy_chain(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_tdes_fvsr_plaintext(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_tdes_fvsr_key(ujson_t *uj);

/**
 * cryptolib tdes sca daisy chain test
 *
 * This SCA penetration test triggers num_iterations cryptolib TDES operations
 * using daisy chaining meaning that the output is copied to the input.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_tdes_daisy_chain(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_hmac_fvsr_plaintext(ujson_t *uj);

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
status_t handle_cryptolib_sca_sym_hmac_fvsr_key(ujson_t *uj);

/**
 * cryptolib hmac sca daisy chain test
 *
 * This SCA penetration test triggers num_iterations cryptolib HMAC operations
 * using daisy chaining meaning that the output is copied to the input.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_hmac_daisy_chain(ujson_t *uj);

/**
 * cryptolib drbg generate sca batch test
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
status_t handle_cryptolib_sca_sym_drbg_generate_batch(ujson_t *uj);

/**
 * cryptolib drbg sca reseed
 *
 * This reseeds the DRBG with the gievn entropy.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_drbg_reseed(ujson_t *uj);

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib SCA firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym_init(ujson_t *uj);

/**
 * CryptoLib SCA command handler.
 *
 * Command handler for the CryptoLib SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_sca_sym(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_CRYPTOLIB_SCA_SYM_H_
