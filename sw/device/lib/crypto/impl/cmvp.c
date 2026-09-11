// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/cmvp.h"

#include "sw/device/lib/crypto/impl/status.h"

#ifdef FIPS_MODE

static void cmvp_start_service(otcrypto_cmvp_service_indicator_t indicator) {
  crypto_state_t *state = NULL;
  if (status_ok(read_state_pointer(&state)) && state != NULL) {
    if (state->cmvp_call_depth == 0) {
      state->cmvp_service_indicator = indicator;
    }
    state->cmvp_call_depth++;
  }
}

void otcrypto_cmvp_start_approved(void) {
  cmvp_start_service(kOtcryptoCmvpApprovedService);
}

void otcrypto_cmvp_start_not_approved(void) {
  cmvp_start_service(kOtcryptoCmvpNotApprovedService);
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
  *indicator = state->cmvp_service_indicator;
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
