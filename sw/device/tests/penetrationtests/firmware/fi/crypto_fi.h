// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTO_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTO_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * AES FI test.
 *
 * This test encrypts a static plaintext with a static key and returns the
 * ciphertext over UART back to the host. The host can define, whether the
 * trigger gets set and unset during(i) loading the key, (ii) loading the
 * plaintext, (iii) encryption, or (iv) when reading back the ciphertext.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_aes(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Crypto FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_init(ujson_t *uj);

/**
 * KMAC FI test.
 *
 * This test absorbs a static message with a static key and returns the
 * digest over UART back to the host. The host can define, whether the
 * trigger gets set and unset during(i) loading the key, (ii) absorbing, or
 * (iii) squeezing.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_kmac(ujson_t *uj);

/**
 * KMAC State FI test.
 *
 * Try to inject a fault into the KMAC state.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_kmac_state(ujson_t *uj);

/**
 * SHA3 FI test.
 *
 * This test absorbs a static message and returns the
 * digest over UART back to the host. The host can define, whether the
 * trigger gets set and unset during(i) loading the start, (ii) absorbing, or
 * (iii) squeezing.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_sha3(ujson_t *uj);

/**
 * HMAC FI test.
 *
 * Receive message & trigger configuration from host. Perform SHA2 or HMAC
 * operation and return the digest back to the host.
 *
 * There are triggers over each interface function.
 * The HMAC has the option to swap the endianness of its message, key, or
 * digest, and it accepts its mode to be in SHA256, SHA384, or SHA512. Enable
 * hmac means that HMAC is used, otherwise SHA2 is used.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_hmac(ujson_t *uj);

/**
 * Shadow Register Access FI test.
 *
 * In this test, faults are injected when accessing KMAC shadow registers.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_shadow_reg_access(ujson_t *uj);

/**
 * Shadow Register Read FI test.
 *
 * In this test, faults are injected when reading the AES and KMAC shadow
 * registers.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi_shadow_reg_read(ujson_t *uj);

/**
 * Crypto FI command handler.
 *
 * Command handler for the Crypto FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_crypto_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTO_FI_H_
