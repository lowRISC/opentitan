// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/entropy_src.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/entropy_kat.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 't', 's')

static status_t lock_on_entropy_err(status_t res) {
#ifdef FIPS_MODE
  if (res.value != kHardenedBoolTrue) {
    crypto_state_t *state = NULL;
    HARDENED_TRY(read_state_pointer(&state));
    if (state->locked_state != kHardenedByteBoolTrue) {
      state->locked_state = kOtcryptoLockStateEntropy;
    }
  }
#endif
  return res;
}

otcrypto_status_t otcrypto_entropy_init(void) {
#ifdef FIPS_MODE
  crypto_state_t *state = NULL;
  HARDENED_TRY(read_state_pointer(&state));
  if (launder32(state->locked_state) != kHardenedByteBoolFalse &&
      launder32(state->locked_state) != kOtcryptoLockStateEntropy) {
    return OTCRYPTO_FATAL_ERR;
  }
  state->locked_state = kHardenedByteBoolTrue;
  HARDENED_TRY(entropy_src_sha3_conditioning_kat());
  state->locked_state = kOtcryptoLockStateEntropy;
#endif  // FIPS_MODE

  HARDENED_TRY(entropy_complex_init(kHardenedBoolTrue));

#ifdef FIPS_MODE
  HARDENED_TRY(otcrypto_entropy_health_test_config_check());
  state->locked_state = kHardenedByteBoolFalse;
#endif  // FIPS_MODE

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_entropy_check(void) {
  HARDENED_TRY(lock_on_entropy_err(entropy_complex_check(kHardenedBoolTrue)));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_entropy_health_test_config_check(void) {
  HARDENED_TRY(lock_on_entropy_err(
      entropy_complex_health_test_config_check(kHardenedBoolTrue)));
  return OTCRYPTO_OK;
}
