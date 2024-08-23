// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_OTBN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_OTBN_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Command handler for the otbn.sca.key_sideload_fvsr test.
 *
 * Side-load 16 fixed vs. random keys from keymanager to OTBN.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_key_sideload_fvsr(ujson_t *uj);

/**
 * Select the OTBN app to load.
 *
 * Currently, only the P256KeyFromSeed application is supported.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_app_select(ujson_t *uj);

/**
 * Enable or disable masking.
 *
 * This command handler allows to enable or disable the masking. When masking is
 * turned on, a random 320-bit mask is generated for  the seed share 1. The mask
 * is 0 when masking is turned off.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_en_masks(ujson_t *uj);

/**
 * Set the constant C.
 *
 * This command handler allows the host to set the constant C to generate the
 * random key.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_set_c(ujson_t *uj);

/**
 * Set the seed share 0.
 *
 * Allows the host to set the 320-bit seed share 0 that is used for the key
 * generation.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_set_seed(ujson_t *uj);

/**
 * Starts the P-256 ECDSA Key Generation from a key in batch mode.
 *
 * Num_traces fixed vs random keys are generated using the SCA PRNG and
 * for each key the key generation operation on OTBN is started.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(ujson_t *uj);

/**
 * Starts the P-256 ECDSA Key Generation from a seed in batch mode.
 *
 * Num_traces fixed vs random seeds are generated using the SCA PRNG and
 * for each seed the key generation operation on OTBN is started.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(ujson_t *uj);

/**
 * Initializes the Keymanager used for the OTBN SCA tests.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_init_keymgr(ujson_t *uj);

/**
 * Initializes the OTBN SCA test on the device.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_init(ujson_t *uj);

/**
 * OTBN SCA command handler.
 *
 * Command handler for the OTBN SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_OTBN_SCA_H_
