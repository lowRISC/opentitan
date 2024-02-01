// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_AST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_AST_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Check that the AST is in the expected state.
 *
 * @param lc_state The current life cycle state.
 *
 * @return an error if the AST is not in the expected state.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ast_check(lifecycle_state_t lc_state);

/**
 * Reports whether the AST has been initialized and the `AST_INIT_DONE`
 * flag is set.
 *
 * @return a hardened bool representing the state of `AST_INIT_DONE`.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t ast_init_done(void);

/**
 * Conditionally patch the AST registers using data stored in an info partition
 * used to store manufacturing information.
 *
 * The patch is skipped if any of the first to AST words stored in the info
 * partition are equivalent to 0 or UINT32_MAX.
 *
 * This function also calls `ast_check()` before returning.
 *
 * @param lc_state The current life cycle state.
 *
 * @return an error if the AST is not in the expected state.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ast_patch(lifecycle_state_t lc_state);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_AST_H_
