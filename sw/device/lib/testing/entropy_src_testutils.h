// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_SRC_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_SRC_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_entropy_src.h"

/**
 * Initializes the entropy_src in firmware override mode.
 *
 * CSRNG and EDN instances are not initialized by calling this function compared
 * to the test init functions in entropy_testutils.
 *
 * @param entropy_src Entropy source handle.
 * @param buffer_threshold Firmware override buffer threshold.
 * @param firmware_override_enable Set to true to output entropy data to
 * registers instead of the CSRNG block.
 * @param bypass_conditioner Set to true to bypass the entropy_src conditioner.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_src_testutils_fw_override_enable(
    dif_entropy_src_t *entropy_src, uint8_t buffer_threshold,
    bool firmware_override_enable, bool bypass_conditioner);

/**
 * Drain the `entropy_src` FW override mode observe FIFO.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_src_testutils_drain_observe_fifo(
    dif_entropy_src_t *entropy_src);

/**
 * Waits for the entropy_src to reach a certain state.
 *
 * @param entropy_src Entropy source handle.
 * @param state Entropy source target FSM state.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_src_testutils_wait_for_state(
    const dif_entropy_src_t *entropy_src, dif_entropy_src_main_fsm_t state);

/**
 * Disables all entropy source health tests.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_src_testutils_disable_health_tests(
    dif_entropy_src_t *entropy_src);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_SRC_TESTUTILS_H_
