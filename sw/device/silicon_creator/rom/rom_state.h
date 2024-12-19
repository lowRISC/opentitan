// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_STATE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_STATE_H_

#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The ROM state API allows for declaring ROM states and their associated
 * callbacks. A ROM state callback defines which new state the ROM should
 * transition to if the current state executes successfully. The
 * `rom_state_fsm()` function walks through the ROM defines states, runs
 * the current state callback and transitions to the next state.
 *
 * Silicon creators can customize a ROM state execution flow through pre-run
 * post-run callback hooks. Pre-run hooks are unconditionally called before a
 * state callback is executed and can modify the state argument. Post-run hooks
 * run only after the state callback successfully completed, and can also modify
 * the state associated argument. The ROM transitions to the next state defined
 * by the current state callback, if and only if the post-run hook returns
 * without errors.
 *
 * By default, the pre-run and post-run hooks are weakly defined symbols that do
 * nothing. They can be overriden by silicon creators, through an external
 * repository. See the corresponding documentation and example in
 * `sw/device/silicon_creator/rom/hooks/`
 */

/**
 * A ROM state.
 */
typedef uint32_t rom_state_t;

/**
 * A ROM state hook.
 * ROM state hooks are called prior and after the state run callback.
 * They can be overridden by silicon creator implementation, through an external
 * repository.
 *
 * @param arg The ROM state argument.
 */
typedef OT_WARN_UNUSED_RESULT rom_error_t rom_state_hook_cb(void *arg);

/**
 * A ROM state run callback.
 * This is the main callback for a ROM state. It can not be overridden by
 * silicon creator hooks, unlike ROM state hooks.
 *
 * @param arg The ROM state callback and hooks argument. This pointer is shared
 *            between a state run callback and hooks, and will typically point
 *            to a static structure or variable.
 * @param[out] next_state The next state the ROM should transition to.
 */
typedef OT_WARN_UNUSED_RESULT rom_error_t
rom_state_run_cb(void *arg, rom_state_t *next_state);

/**
 * A ROM state Control Flow Integrity (CFI) set of counters indexes.
 * Four CFI counters per ROM state are maintained in a single ROM state CFI
 * array, as defined and intialized by the ROM_STATE_CFI_TABLE_ENTRIES_ macro.
 * This structure keeps track of those four ROM state indexes in that table.
 * The ROM state CFI counter, indexed by the `state_index` field in this
 * structure, gets incremented as the ROM state machine goes through the three
 * steps in the ROM state sequence and calls the pre_run, run and post_run
 * functions.
 * The pre_run, run and post_run CFI counters are initialized by the ROM state
 * machine, before calling their associated functions.
 */
typedef struct rom_state_cfi {
  size_t state_index;    // The overall ROM state index into the CFI table.
  size_t pre_run_index;  // The pre_run hook CFI index
  size_t post_run_index;
  size_t run_index;
} rom_state_cfi_t;

/**
 * A ROM state callback
 */
typedef struct rom_state_cb {
  rom_state_t state;
  rom_state_cfi_t cfi;
  void *arg;
  rom_state_hook_cb *pre_run;
  rom_state_hook_cb *post_run;
  rom_state_run_cb *run;
} rom_state_cb_t;

// clang-format off
#define ROM_STATE_PRE_HOOK_WEAK_(state_)             \
  OT_WEAK OT_WARN_UNUSED_RESULT                      \
  rom_error_t rom_state_pre_##state_(void *arg) {    \
    return kErrorOk;                                 \
  }

#define ROM_STATE_POST_HOOK_WEAK_(state_)           \
  OT_WEAK OT_WARN_UNUSED_RESULT                     \
  rom_error_t rom_state_post_##state_(void *arg) {  \
    return kErrorOk;                                \
  }

#define ROM_STATE_CALLBACKS_(state_, value_, run_, run_arg_)     \
  ROM_STATE_PRE_HOOK_WEAK_(state_)                               \
  ROM_STATE_POST_HOOK_WEAK_(state_)

#define ROM_STATE_VALUES_(state_, value_, run_, run_arg) state_ = value_,
#define ROM_STATE_CFI_INDEXES_(state_, value_, run_, run_arg) \
  state_##_cfi_index,                                         \
  state_##_pre_run_cfi_index,                                 \
  state_##_run_cfi_index,                                     \
  state_##_post_run_cfi_index,

#define ROM_STATE_CFI_ENTRIES_(state_, value_, run_, run_arg)   \
  {                                                             \
      .state_index =  state_##_cfi_index,                       \
      .pre_run_index =  state_##_pre_run_cfi_index,             \
      .post_run_index =  state_##_post_run_cfi_index,           \
      .run_index =  state_##_run_cfi_index,                     \
  }

#define ROM_STATE_CFI_TABLE_ENTRIES_(state_, value_, run_, run_arg_) 0, 0, 0, 0,

#define ROM_STATE_TABLE_ENTRIES_(state_, value_, run_, run_arg_)        \
  {                                                                     \
      .state = state_,                                                  \
      .cfi = ROM_STATE_CFI_ENTRIES_(state_, value_, run_, run_arg_),    \
      .pre_run = rom_state_pre_##state_,                                \
      .post_run = rom_state_post_##state_,                              \
      .run = run_,                                                      \
      .arg = run_arg_,                                                  \
  },

/**
 * Binds a hook implementation to a ROM state, in order for it to be run
 * before the state's run callback.
 *
 * This macro overrides the default, empty pre-run hook for a given state.
 */
#define ROM_STATE_PRE_HOOK(state_, hook_)           \
  OT_WARN_UNUSED_RESULT                             \
  rom_error_t rom_state_pre_##state_(void *arg) {   \
    return hook_(arg);                              \
  }

/**
 * Binds a hook implementation to a ROM state, in order for it to be run
 * after the state's run callback.
 *
 * This macro overrides the default, empty post-run hook for a given state.
 */
#define ROM_STATE_POST_HOOK(state_, hook_)          \
  OT_WARN_UNUSED_RESULT                             \
  rom_error_t rom_state_post_##state_(void *arg) {  \
    return hook_(arg);                              \
  }

/**
 * The ROM states table.
 *
 * This macro declares and defines:
 * - All ROM state values as an enum.
 * - For each ROM state, its callback, its pre-run and post-run,
 *   weakly-defined and overridable hooks, and its argument.
 * - The ROM states array.
 * - The ROM states CFI indexes.
 *
 * @param table_name_ The ROM states array name. This will be defined as a
 *                    static, constant array of `rom_state_cb_t` entries.
 * @param table_cnt_ The exact number of entries in the states array.
 * @param TABLE_ The ROM state table definition. `TABLE_` is C macro that
 *               takes another macro as its argument. The macro passed to
 *               `TABLE_` takes 4 arguments in order to create a ROM state
 *               tuple: one identifier, one value, one run callback and one
 *               argument to pass to the callback. The created tuple is used to
 *               define and declare a ROM state related structure or variable.
 */
#define ROM_STATE_INIT_TABLE(table_name_, table_cnt_, TABLE_)   \
  enum { TABLE_(ROM_STATE_VALUES_) };                           \
  enum { TABLE_(ROM_STATE_CFI_INDEXES_) };                      \
  TABLE_(ROM_STATE_CALLBACKS_)                                  \
  uint32_t table_name_##_cfi[] = {TABLE_(ROM_STATE_CFI_TABLE_ENTRIES_)}; \
  static const rom_state_cb_t table_name_[table_cnt_] = {TABLE_(ROM_STATE_TABLE_ENTRIES_) }
// clang-format on

/**
 * The ROM state machine walker.
 *
 * ROM implementations call this function with the initial ROM state, and it
 * walk through the ROM states defined in @states_callback.
 * When transitioning to a ROM state, this function will first call the pre-run
 * hook for the state, then the state run callback and finally the post-run
 * hook. If any one of these three call returns an error, `rom_state_fsm`
 * returns and propagates the error.
 *
 * @param states_callbacks The array of all ROM states callbacks.
 * @param states_callbacks_cnt The number of entries in states_callbacks.
 * @param init_state The initial state of the ROM.
 */
OT_WARN_UNUSED_RESULT rom_error_t rom_state_fsm_walk(
    const rom_state_cb_t states_callbacks[], const size_t state_callbacks_cnt,
    const rom_state_t init_state, uint32_t state_cfi_table[]);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_STATE_H_
