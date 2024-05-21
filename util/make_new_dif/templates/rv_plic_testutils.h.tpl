// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_${ip.name_upper}_TEST_UTILS_${ip.name_upper}_TESTUTILS_H_
#define OPENTITAN_SW_IP_${ip.name_upper}_TEST_UTILS_${ip.name_upper}_TESTUTILS_H_

#include "sw/ip/${ip.name_snake}/dif/dif_${ip.name_snake}.h"

/**
 * Enables a range of IRQs at the ${ip.name_long_upper}.
 *
 * All interrupts between the first and the last index (inclusive
 * of both), which are provided as arguments are enabled. It also sets the
 * threshold for the target to kDifRvPlicMinPriority and picks the priority of
 * the interrupts randomly between kDifRvPlicMinPriority + 1 and
 * kDifRvPlicMaxPriority. We may however, revisit this approach in future as
 * testing needs evolve.
 * @param plic A ${ip.name_long_upper} handle.
 * @param target An interrupt target.
 * @param start_irq_id The first interrupt index.
 * @param start_irq_id The last interrupt index.
 */
void ${ip.name_snake}_testutils_irq_range_enable(dif_${ip.name_snake}_t *plic,
                                        dif_${ip.name_snake}_target_t target,
                                        dif_${ip.name_snake}_irq_id_t start_irq_id,
                                        dif_${ip.name_snake}_irq_id_t end_irq_id);

#endif  // OPENTITAN_SW_IP_${ip.name_upper}_TEST_UTILS_${ip.name_upper}_TESTUTILS_H_
