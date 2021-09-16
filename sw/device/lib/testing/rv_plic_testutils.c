// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rv_plic_testutils.h"

#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rand_testutils.h"

void rv_plic_testutils_irq_range_enable(dif_rv_plic_t *plic,
                                        dif_rv_plic_target_t target,
                                        dif_rv_plic_irq_id_t start_irq_id,
                                        dif_rv_plic_irq_id_t end_irq_id) {
  for (dif_rv_plic_irq_id_t irq_id = start_irq_id; irq_id <= end_irq_id;
       ++irq_id) {
    uint32_t priority = rand_testutils_gen32_range(kDifRvPlicMinPriority + 1,
                                                   kDifRvPlicMaxPriority);
    CHECK(dif_rv_plic_irq_set_priority(plic, irq_id, priority) == kDifRvPlicOk);
    CHECK(dif_rv_plic_irq_set_enabled(plic, irq_id, target,
                                      kDifRvPlicToggleEnabled) == kDifRvPlicOk);
  }
  CHECK(dif_rv_plic_target_set_threshold(plic, target, kDifRvPlicMinPriority) ==
        kDifRvPlicOk);
}
