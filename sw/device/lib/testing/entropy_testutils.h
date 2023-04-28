// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"

/**
 * Returns default entropy source configuration.
 */
dif_entropy_src_config_t entropy_testutils_config_default(void);

/**
 * Initializes the entropy complex in auto-request mode.
 *
 * Initializes the CSRNG, EDN0, and EDN1 in automatic request mode, with EDN1
 * providing highest-quality entropy and EDN0 providing lower-quality entropy.
 * The entropy source must have been initialized separately before calling this
 * function.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_auto_mode_init(void);

/**
 * Initializes the entropy complex to serve random bits to EDN0 and EDN1.
 *
 * Initializes entropy_src, csrng, EDN0 and EDN1 with default boot time
 * configuration to enable entropy distribution for testing purposes.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_boot_mode_init(void);

/**
 * Initializes the entropy_src in firmware override mode.
 *
 * CSRNG and EDN instances are not initialized by calling this function compared
 * to the other test init functions.
 *
 * @param entropy_src Entropy source handle.
 * @param buffer_threshold Firmware override buffer threshold.
 * @param firmware_override_enable Set to true to output entropy data to
 * registers instead of the CSRNG block.
 * @param bypass_conditioner Set to true to bypass the entropy_src conditioner.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_fw_override_enable(dif_entropy_src_t *entropy_src,
                                              uint8_t buffer_threshold,
                                              bool firmware_override_enable,
                                              bool bypass_conditioner);

/**
 * Waits for the entropy_src to reach a certain state.
 *
 * @param entropy_src Entropy source handle.
 * @param state Entropy source target FSM state.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_wait_for_state(const dif_entropy_src_t *entropy_src,
                                          dif_entropy_src_main_fsm_t state);

/**
 * Stops all entropy complex blocks.
 *
 * Stops EDN and CSRNG instances before stopping the entropy source.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_stop_all(void);

/**
 * Throws test assertion if there are any errors detected in any of the entropy
 * blocks.
 *
 * Note that the encoding of the error codes printed in the log follow the
 * respective DIF error enum mapping, which may be different to the bit mapping
 * in the error registers.
 *
 * @param entropy_src Entropy source handle.
 * @param csrng CSRNG handle.
 * @param edn0 EDN0 handle.
 * @param edn1 EDN1 handle.
 * @return The result of the operation wrapped on a status_t.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_error_check(const dif_entropy_src_t *entropy_src,
                                       const dif_csrng_t *csrng,
                                       const dif_edn_t *edn0,
                                       const dif_edn_t *edn1);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
