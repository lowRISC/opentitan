// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom_state.h"

#include "sw/device/silicon_creator/lib/shutdown.h"

static OT_WARN_UNUSED_RESULT rom_error_t rom_state_get_state_cb(
    const rom_state_cb_t state_callbacks[], const size_t state_callbacks_cnt,
    const rom_state_t state, const rom_state_cb_t **state_cb) {
  // TODO Start from a random index
  for (size_t idx = 0; idx < state_callbacks_cnt; idx++) {
    if (launder32(state_callbacks[idx].state) != state) {
      continue;
    }

    HARDENED_CHECK_EQ(state_callbacks[idx].state, state);

    *state_cb = &state_callbacks[idx];
    HARDENED_CHECK_EQ(*state_cb, &state_callbacks[idx]);

    return kErrorOk;
  }

  return kErrorRomBootFailed;
}

OT_WARN_UNUSED_RESULT rom_error_t rom_state_fsm_walk(
    const rom_state_cb_t state_callbacks[], const size_t state_callbacks_cnt,
    const rom_state_t init_state) {
  rom_state_t next_state = init_state;

  while (true) {
    rom_state_t current_state = next_state;
    const rom_state_cb_t *current_state_cb = NULL;

    HARDENED_RETURN_IF_ERROR(
        rom_state_get_state_cb(state_callbacks, state_callbacks_cnt,
                               current_state, &current_state_cb));

    // Pre run hook.
    HARDENED_RETURN_IF_ERROR(current_state_cb->pre_run(current_state_cb->arg));

    // State run callback.
    HARDENED_RETURN_IF_ERROR(
        current_state_cb->run(current_state_cb->arg, &next_state));
    HARDENED_CHECK_NE(current_state, next_state);

    // Post run hooks.
    HARDENED_RETURN_IF_ERROR(current_state_cb->post_run(current_state_cb->arg));
  }
}
