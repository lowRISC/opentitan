// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"

/**
 * Initializes the top-specific entropy source with default configuration.
 *
 * On Earlgrey, it initializes the entropy_src.
 * On Darjeeling, this is a no-op.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_entropy_src_init(void);

/**
 * Initializes the entropy complex in auto-request mode.
 *
 * Initializes the entropy source, CSRNG, EDN0, and EDN1 in automatic request
 * mode, with EDN1 providing highest-quality entropy and EDN0 providing
 * lower-quality entropy.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_auto_mode_init(void);

/**
 * Initializes the entropy complex to serve random bits to EDN0 and EDN1.
 *
 * Initializes the entropy source, csrng, EDN0 and EDN1 with default boot time
 * configuration to enable entropy distribution for testing purposes.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_boot_mode_init(void);

/**
 * Stops EDN instances and CSRNG.
 *
 * Stops EDN instances before stopping CSRNG.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_stop_csrng_edn(void);

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
 * @param csrng CSRNG handle.
 * @param edn0 EDN0 handle.
 * @param edn1 EDN1 handle.
 * @return The result of the operation wrapped on a status_t.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_testutils_error_check(const dif_csrng_t *csrng,
                                       const dif_edn_t *edn0,
                                       const dif_edn_t *edn1);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
