// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_

#include "sw/device/lib/dif/dif_edn.h"

/**
 * Returns randomized seed material.
 *
 * @param disable_rand If set, a struct containing default values is returned.
 * @return A seed material struct containing the length and the seed material.
 */
OT_WARN_UNUSED_RESULT
dif_edn_seed_material_t edn_testutils_seed_material_build(bool disable_rand);

/**
 * Returns a randomized EDN auto mode configuration.
 *
 * @param disable_rand If set, a struct containing default values is returned.
 * @return A parameter struct containing the settings required for auto mode.
 */
OT_WARN_UNUSED_RESULT
dif_edn_auto_params_t edn_testutils_auto_params_build(bool disable_rand);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
