// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_OTBN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_OTBN_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

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
 * otbn.sca.ecdsa256.sign command handler.
 *
 * Runs a ECDSA 256 sign operation, used to measure whether the operation
 * leakes secret information.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecdsa_p256_sign(ujson_t *uj);

/**
 * otbn.sca.ecdsa256.sign_batch command handler.
 *
 * Same as otbn.sca.ecdsa256.sign but in batch mode. Random message, random
 * key, and random secret is used.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecdsa_p256_sign_batch(ujson_t *uj);

/**
 * otbn.sca.ecdsa256.sign_fvsr_batch command handler.
 *
 * Same as otbn.sca.ecdsa256.sign but in batch mode. Fixed or random message,
 * fixed or random key, and fixed or random secret is used.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_ecdsa_p256_sign_fvsr_batch(ujson_t *uj);

/**
 * Initializes the OTBN SCA test on the device.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_pentest_init(ujson_t *uj);

/**
 * Initializes the Keymanager used for the OTBN SCA tests.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_pentest_init_keymgr(ujson_t *uj);

/**
 * otbn.sca.insn.carry_flag command handler.
 *
 * Receive big_num from host. On OTBN, add big_num + big_num and get the
 * carry flag. If the carry flag is not set, return the result. If the carry
 * flag is set, return random number. Checks whether carry flag is leaking.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_insn_carry_flag(ujson_t *uj);

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
 * Command handler for the otbn.sca.rsa512_decrypt test.
 *
 * RSA512 decryption side-channel test. Get mod, exp, and msg from uJSON.
 * Perform RSA512 decryption and send back the message.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_rsa512_decrypt(ujson_t *uj);

/**
 * Command handler for the otbn.sca.combi_ops test.
 *
 * Loads two fixed values to the OTBN and performs several operations.
 * Each operation also has an output that the test sends back.
 * Each 32-bit fixed value is copied eight times to fill a 256-bit register.
 *
 * The results are those of
 * - the loading of the first input
 * - the bn.mov instruction of the first input
 * - the addition between the first and second input
 * - the subtraction between the first and second input
 * - the xor between the first and second input
 * - the left shift by one of the first input
 * - the multiplication (using bn.mulqacc) between the first 64-bits of each
 * input
 * - the comparison of the two inputs (8 means the comparison was succesful and
 * 4 means it was not) The above is done under a trigger signal.
 *
 * A second trigger window can be chosen which is over the wiping of the OTBN.
 *
 * The print_flag can be set to false to print a small success value instead of
 * the full response.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_combi_operations_batch(ujson_t *uj);

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
