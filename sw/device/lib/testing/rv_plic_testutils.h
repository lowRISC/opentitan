// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RV_PLIC_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RV_PLIC_TESTUTILS_H_

#include "sw/device/lib/dif/dif_rv_plic.h"

/**
 * Enables a range of IRQs at the PLIC.
 *
 * All interrupts between the first and the last index (inclusive
 * of both), which are provided as arguments are enabled. It also sets the
 * threshold for the target to kDifRvPlicMinPriority and picks the priority of
 * the interrupts randomly between kDifRvPlicMinPriority + 1 and
 * kDifRvPlicMaxPriority. We may however, revisit this approach in future as
 * testing needs evolve.
 * @param plic A PLIC handle.
 * @param target An interrupt target.
 * @param start_irq_id The first interrupt index.
 * @param start_irq_id The last interrupt index.
 */
void rv_plic_testutils_irq_range_enable(dif_rv_plic_t *plic,
                                        dif_rv_plic_target_t target,
                                        dif_rv_plic_irq_id_t start_irq_id,
                                        dif_rv_plic_irq_id_t end_irq_id);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RV_PLIC_TESTUTILS_H_
