// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/cmvp.h"

#include "sw/device/lib/crypto/impl/status.h"

#ifdef FIPS_MODE

uint8_t otcrypto_cmvp_enter(otcrypto_cmvp_service_indicator_t indicator) {
  crypto_state_t *state = NULL;
  if (status_ok(read_state_pointer(&state)) && state != NULL) {
    if (state->cmvp_call_depth == 0) {
      state->cmvp_service_indicator = (uint8_t)indicator;
    }
    state->cmvp_call_depth++;
    return state->cmvp_call_depth;
  }
  return 0;
}

void otcrypto_cmvp_cleanup(const uint8_t *expected_depth) {
  if (expected_depth == NULL || *expected_depth == 0) {
    return;
  }
  crypto_state_t *state = NULL;
  if (status_ok(read_state_pointer(&state)) && state != NULL) {
    if (state->cmvp_call_depth >= *expected_depth) {
      state->cmvp_service_indicator = (uint8_t)kOtcryptoCmvpNotApprovedService;
    }
    state->cmvp_call_depth = (uint8_t)(*expected_depth - 1);
  }
}

void otcrypto_cmvp_start_approved(void) {
  (void)otcrypto_cmvp_enter(kOtcryptoCmvpApprovedService);
}

void otcrypto_cmvp_start_not_approved(void) {
  (void)otcrypto_cmvp_enter(kOtcryptoCmvpNotApprovedService);
}

void otcrypto_cmvp_override_not_approved(void) {
  crypto_state_t *state = NULL;
  if (status_ok(read_state_pointer(&state)) && state != NULL) {
    state->cmvp_service_indicator = kOtcryptoCmvpNotApprovedService;
  }
}

void otcrypto_cmvp_end_service(void) {
  crypto_state_t *state = NULL;
  if (status_ok(read_state_pointer(&state)) && state != NULL) {
    if (state->cmvp_call_depth > 0) {
      state->cmvp_call_depth--;
    }
  }
}

otcrypto_status_t otcrypto_cmvp_service_indicator(
    otcrypto_cmvp_service_indicator_t *indicator) {
  if (indicator == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  crypto_state_t *state = NULL;
  if (!status_ok(read_state_pointer(&state)) || state == NULL) {
    *indicator = kOtcryptoCmvpNoService;
    return OTCRYPTO_OK;
  }
  *indicator = (otcrypto_cmvp_service_indicator_t)state->cmvp_service_indicator;
  state->cmvp_service_indicator = kOtcryptoCmvpNoService;
  state->cmvp_call_depth = 0;
  return OTCRYPTO_OK;
}

#else  // !defined(FIPS_MODE)

otcrypto_status_t otcrypto_cmvp_service_indicator(
    otcrypto_cmvp_service_indicator_t *indicator) {
  if (indicator == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *indicator = kOtcryptoCmvpNoService;
  return OTCRYPTO_OK;
}

#endif  // FIPS_MODE
