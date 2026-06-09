// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/state.h"

namespace test {
extern "C" {

static crypto_state_t *stored_state = nullptr;
static crypto_state_t default_state = {
    .imem_cache = 0,
    .kat_state = 0,
    .security_level = kOtcryptoKeySecurityLevelLow,
    .self_check_state = kHardenedBoolFalse,
    .locked_state = kHardenedBoolFalse,
};

otcrypto_status_t init_state(otcrypto_state_t *state,
                             otcrypto_key_security_level_t security_level) {
  crypto_state_t *internal_state = (crypto_state_t *)state;
  memset(internal_state, 0, sizeof(*internal_state));
  internal_state->locked_state = kHardenedBoolFalse;
  internal_state->self_check_state = kHardenedBoolFalse;
  internal_state->security_level = security_level;
  return OTCRYPTO_OK;
}

otcrypto_status_t store_state(otcrypto_state_t *state) {
  stored_state = (crypto_state_t *)state;
  return OTCRYPTO_OK;
}

status_t read_state_pointer(crypto_state_t **state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (stored_state == nullptr) {
    *state = &default_state;
  } else {
    *state = stored_state;
  }
  return OTCRYPTO_OK;
}

#ifdef FIPS_MODE
otcrypto_status_t stateful_health_check(kat_bits_t kat_bit) {
  return OTCRYPTO_OK;
}
#endif

}  // extern "C"
}  // namespace test
