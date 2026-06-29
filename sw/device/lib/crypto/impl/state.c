// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/state.h"

#include <string.h>

#include "hw/top/dt/otbn.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "hw/top/otbn_regs.h"  // Generated

static const dt_otbn_t kOtbnDt = kDtOtbn;

static inline uint32_t otbn_base(void) {
  return dt_otbn_primary_reg_block(kOtbnDt);
}

otcrypto_status_t store_state(const crypto_state_t *state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t words[OTBN_SCRATCH_MULTIREG_COUNT] = {0};
  memcpy(words, state, sizeof(words));
  uint32_t base = otbn_base() + OTBN_SCRATCH_0_REG_OFFSET;
  for (size_t i = 0; i < OTBN_SCRATCH_MULTIREG_COUNT; ++i) {
    abs_mmio_write32(base + i * sizeof(uint32_t), words[i]);
  }
  return OTCRYPTO_OK;
}

status_t read_state(crypto_state_t *state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  memset(state, 0, sizeof(*state));
  uint32_t words[OTBN_SCRATCH_MULTIREG_COUNT];
  uint32_t base = otbn_base() + OTBN_SCRATCH_0_REG_OFFSET;
  for (size_t i = 0; i < OTBN_SCRATCH_MULTIREG_COUNT; ++i) {
    words[i] = abs_mmio_read32(base + i * sizeof(uint32_t));
  }
  memcpy(state, words, sizeof(words));
  if (state->security_level == 0) {
    return OTCRYPTO_RECOV_ERR;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t init_state(otcrypto_key_security_level_t security_level) {
  crypto_state_t internal_state = {
      .imem_cache = 0,
      .kat_state = 0,
      .security_level = security_level,
      .self_check_state = kHardenedBoolFalse,
      .locked_state = kHardenedBoolFalse,
      .csrng_instantiated = kHardenedBoolFalse,
      .csrng_is_default = kHardenedBoolFalse,
#ifdef FIPS_MODE
      .cmvp_service_indicator = kOtcryptoCmvpNoService,
      .cmvp_call_depth = 0,
#endif
  };
  return store_state(&internal_state);
}

#ifdef FIPS_MODE

otcrypto_status_t stateful_health_check(kat_bits_t kat_bit) {
  crypto_state_t state;
  HARDENED_TRY(read_state(&state));

  // If we are in a locked state, the health check returns a fatal error
  if (state.locked_state == kHardenedBoolTrue) {
    return OTCRYPTO_FATAL_ERR;
  }

  // The self-integrity check uses SHA-2, so the SHA-2 KAT
  // must be allowed to execute before the self-integrity check has completed.
  if (kat_bit != kTestHashSha512Bit &&
      state.self_check_state == kHardenedBoolFalse) {
    return OTCRYPTO_RECOV_ERR;
  }

  uint32_t mask = (1UL << kat_bit);

  if ((state.kat_state & mask) == 0) {
    state.kat_state |= mask;  // Re-entrance lock
    HARDENED_TRY(store_state(&state));

    kat_id_t test_id = {.flags = mask};
    status_t result = run_kats(test_id);

    // If the KAT failed, lock the cryptolib
    if (result.value != kHardenedBoolTrue) {
      HARDENED_TRY(read_state(&state));
      state.locked_state = kHardenedBoolTrue;
      HARDENED_TRY(store_state(&state));
      return result;
    }
  }

  return OTCRYPTO_OK;
}

#endif  // FIPS_MODE
