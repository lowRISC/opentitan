// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/state.h"

namespace test {
extern "C" {

static crypto_state_t stored_state = {
    .imem_cache = 0,
    .kat_state = 0,
    .security_level = kOtcryptoKeySecurityLevelLow,
    .self_check_state = kHardenedByteBoolFalse,
    .locked_state = kHardenedByteBoolFalse,
    .csrng_instantiated = kHardenedByteBoolFalse,
    .csrng_is_default = kHardenedByteBoolFalse,
#ifdef FIPS_MODE
    .cmvp_service_indicator = kOtcryptoCmvpNoService,
    .cmvp_call_depth = 0,
#endif
};

otcrypto_status_t init_state(otcrypto_key_security_level_t security_level) {
  memset(&stored_state, 0, sizeof(stored_state));
  stored_state.locked_state = kHardenedByteBoolFalse;
  stored_state.self_check_state = kHardenedByteBoolFalse;
  stored_state.csrng_instantiated = kHardenedByteBoolFalse;
  stored_state.csrng_is_default = kHardenedByteBoolFalse;
#ifdef FIPS_MODE
  stored_state.cmvp_service_indicator = kOtcryptoCmvpNoService;
  stored_state.cmvp_call_depth = 0;
#endif
  stored_state.security_level = (uint16_t)security_level;
  return OTCRYPTO_OK;
}

otcrypto_status_t store_state(const crypto_state_t *state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  stored_state = *state;
  return OTCRYPTO_OK;
}

status_t read_state(crypto_state_t *state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *state = stored_state;
  return OTCRYPTO_OK;
}

#ifdef FIPS_MODE
otcrypto_status_t stateful_health_check(kat_bits_t kat_bit) {
  return OTCRYPTO_OK;
}
#endif

}  // extern "C"
}  // namespace test
