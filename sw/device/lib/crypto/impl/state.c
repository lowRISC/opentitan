// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/state.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "entropy_src_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t kBaseEntropySrc = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR;

otcrypto_status_t init_state(otcrypto_state_t *state,
                             otcrypto_key_security_level_t security_level) {
  crypto_state_t *internal_state = (crypto_state_t *)state;
  internal_state->imem_cache = 0;
  internal_state->kat_state = 0;
  internal_state->locked_state = kHardenedBoolFalse;
  internal_state->self_check_state = kHardenedBoolFalse;
  internal_state->csrng_instantiated = kHardenedBoolFalse;
  internal_state->csrng_is_default = kHardenedBoolFalse;
  internal_state->security_level = security_level;
  return OTCRYPTO_OK;
}

otcrypto_status_t store_state(otcrypto_state_t *state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t state_addr = (uint32_t)state;
  uint16_t state_hi = (uint16_t)(state_addr >> 16);
  uint16_t state_lo = (uint16_t)(state_addr & 0xFFFF);

  abs_mmio_write32(
      kBaseEntropySrc + ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_OFFSET,
      bitfield_field32_write(ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_RESVAL,
                             ENTROPY_SRC_EXTHT_HI_THRESHOLDS_FIPS_THRESH_FIELD,
                             state_hi));
  abs_mmio_write32(
      kBaseEntropySrc + ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET,
      bitfield_field32_write(ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_RESVAL,
                             ENTROPY_SRC_EXTHT_LO_THRESHOLDS_FIPS_THRESH_FIELD,
                             state_lo));
  return OTCRYPTO_OK;
}

status_t read_state_pointer(crypto_state_t **state) {
  if (state == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  uint32_t reg_hi = abs_mmio_read32(kBaseEntropySrc +
                                    ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_OFFSET);
  uint32_t reg_lo = abs_mmio_read32(kBaseEntropySrc +
                                    ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET);

  uint32_t val_hi = bitfield_field32_read(
      reg_hi, ENTROPY_SRC_EXTHT_HI_THRESHOLDS_FIPS_THRESH_FIELD);
  uint32_t val_lo = bitfield_field32_read(
      reg_lo, ENTROPY_SRC_EXTHT_LO_THRESHOLDS_FIPS_THRESH_FIELD);

  if (val_hi == 0xFFFF) {
    *state = NULL;
    return OTCRYPTO_RECOV_ERR;
  }

  uint32_t state_addr = (val_hi << 16) | val_lo;
  *state = (crypto_state_t *)state_addr;

  return OTCRYPTO_OK;
}

#ifdef FIPS_MODE

otcrypto_status_t stateful_health_check(kat_bits_t kat_bit) {
  crypto_state_t *state = NULL;

  HARDENED_TRY(read_state_pointer(&state));

  // If we are in a locked state, the health check returns a fatal error
  if (state->locked_state == kHardenedBoolTrue) {
    return OTCRYPTO_FATAL_ERR;
  }

  // We consider the missing self-integrity case to be a user error, hence we
  // return a recoverable error.
  if (state->self_check_state == kHardenedBoolFalse) {
    return OTCRYPTO_RECOV_ERR;
  }

  uint32_t mask = (1UL << kat_bit);

  if ((state->kat_state & mask) == 0) {
    state->kat_state |= mask;  // Re-entrance lock

    kat_id_t test_id = {.flags = mask};
    status_t result = run_kats(test_id);

    // If the KAT failed, lock the cryptolib
    if (result.value != kHardenedBoolTrue) {
      state->locked_state = kHardenedBoolTrue;
      return result;
    }
  }

  return OTCRYPTO_OK;
}

#endif  // FIPS_MODE
