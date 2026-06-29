// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATE_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATE_H_

#include "sw/device/lib/crypto/impl/kats.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef struct crypto_state {
  uint32_t imem_cache;
  uint32_t kat_state;
  otcrypto_key_security_level_t security_level;
  hardened_bool_t self_check_state;
  hardened_bool_t locked_state;
  hardened_bool_t csrng_instantiated;
  hardened_bool_t csrng_is_default;
  otcrypto_cmvp_service_indicator_t cmvp_service_indicator;
  uint32_t cmvp_call_depth;
} crypto_state_t;

/**
 * Initializes the state structure and stores it in the OTBN scratch registers.
 *
 * @param security_level The security level that is used for the cryptolib
 * itself.
 * @return error on failure.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t init_state(otcrypto_key_security_level_t security_level);

/**
 * Stores the state in the OTBN scratch registers.
 *
 * @param state Pointer to the state to store.
 * @return error on failure.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t store_state(const crypto_state_t *state);

/**
 * Retrieves the state stored in the OTBN scratch registers.
 *
 * @param[out] state Pointer to receive the state.
 * @return error on failure.
 */
OT_WARN_UNUSED_RESULT
status_t read_state(crypto_state_t *state);

/**
 * @brief Ensures the specified Known Answer Test (KAT) is executed exactly
 * once. Checks the state of the cryptolib whether it is locked or whether the
 * self integrity passed.
 *
 * This function provides stateful, lazy evaluation of KATs depending on the
 * build configuration:
 *
 * - **FIPS Build (`FIPS_MODE` defined):** It retrieves the KAT state
 *   stored in the OTBN scratch registers. It checks this state to verify if
 *   the KAT corresponding to `kat_bit` has already passed. If not, it executes
 *   the KAT and securely updates the state bitmask.
 * - **Standard Build (`FIPS_MODE` undefined):** The function simply returns
 * OTCRYPTO_OK and performs no checks.
 *
 * @param kat_bit The specific KAT identifier to execute.
 * @return Result of the operation. Returns `OTCRYPTO_OK` on success, if the
 *         KAT already passed, or if lazy evaluation is disabled. Returns
 *         `OTCRYPTO_FATAL_ERR` if the KAT fails.
 */
#ifndef FIPS_MODE

// Standard build: Stateful KAT evaluation is disabled (non FIPS).
static inline otcrypto_status_t stateful_health_check(kat_bits_t kat_bit) {
  (void)kat_bit;
  return OTCRYPTO_OK;
}

#else

// FIPS build: Evaluates kats in a stateful manner
otcrypto_status_t stateful_health_check(kat_bits_t kat_bit);

#endif  // FIPS_MODE

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATE_H_
