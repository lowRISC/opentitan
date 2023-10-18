// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_

#include "sw/device/lib/dif/dif_edn.h"

/**
 * Returns randomized seed material.
 */
OT_WARN_UNUSED_RESULT
dif_edn_seed_material_t edn_testutils_seed_material_build(void);

/**
 * Returns a randomized EDN auto mode configuration.
 */
OT_WARN_UNUSED_RESULT
dif_edn_auto_params_t edn_testutils_auto_params_build(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
