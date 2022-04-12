// Copyright lowRISC contributors.
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
 * @return an error if the AST is not in the expected state.
 */
rom_error_t ast_check(lifecycle_state_t lc_state);

/**
 * Reports whether the AST has been initialized and the `AST_INIT_DONE`
 * flag is set.
 *
 * @return a hardened bool representing the state of `AST_INIT_DONE`.
 */
hardened_bool_t ast_init_done(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_AST_H_
