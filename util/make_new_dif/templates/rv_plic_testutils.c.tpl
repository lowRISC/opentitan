// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/${ip.name_snake}/test/utils/${ip.name_snake}_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/rv_core_ibex/test/utils/rand_testutils.h"
#include "sw/ip/${ip.name_snake}/dif/dif_${ip.name_snake}.h"
#include "sw/lib/sw/device/runtime/log.h"

void ${ip.name_snake}_testutils_irq_range_enable(dif_${ip.name_snake}_t *plic,
                                        dif_${ip.name_snake}_target_t target,
                                        dif_${ip.name_snake}_irq_id_t start_irq_id,
                                        dif_${ip.name_snake}_irq_id_t end_irq_id) {
  for (dif_${ip.name_snake}_irq_id_t irq_id = start_irq_id; irq_id <= end_irq_id;
       ++irq_id) {
    uint32_t priority = rand_testutils_gen32_range(kDif${ip.name_camel}MinPriority + 1,
                                                   kDif${ip.name_camel}MaxPriority);
    CHECK_DIF_OK(dif_${ip.name_snake}_irq_set_priority(plic, irq_id, priority));
    CHECK_DIF_OK(
        dif_${ip.name_snake}_irq_set_enabled(plic, irq_id, target, kDifToggleEnabled));
  }
  CHECK_DIF_OK(
      dif_${ip.name_snake}_target_set_threshold(plic, target, kDif${ip.name_camel}MinPriority));
}
