// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_

#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Returns the value of the EDN status flag.
 *
 * @param edn An edn DIF handle.
 * @param status Status value to query.
 */
inline bool edn_testutils_get_status(dif_edn_t *edn, uint32_t state_val) {
  uint32_t state;
  dif_result_t res = dif_edn_get_main_state_machine(edn, &state);
  return (res == kDifOk) && (state == state_val);
}

/**
 * Waits for the given EDN status flag to be set the given value.
 *
 * @param edn An edn DIF handle.
 * @param flag Status flag value.
 * @param status The status value.
 * @param timeout_usec Timeout in microseconds.
 */
#define EDN_TESTUTILS_WAIT_FOR_STATUS(edn_, state_, flag_, timeout_usec_)  \
  IBEX_TRY_SPIN_FOR(edn_testutils_get_status((edn_), (state_)) == (flag_), \
                    (timeout_usec_))

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
 * @param res_itval If > 0, the reseed interval is set to res_itval.
 * @param glen_val If > 0, the generate length is set to glen_val.
 * @return A parameter struct containing the settings required for auto mode.
 */
OT_WARN_UNUSED_RESULT
dif_edn_auto_params_t edn_testutils_auto_params_build(bool disable_rand,
                                                      unsigned int res_itval,
                                                      unsigned int glen_val);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_EDN_TESTUTILS_H_
