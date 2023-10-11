// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_irqs.h"

#include <zephyr/devicetree.h>
#include <zephyr/sys/util_macro.h>

#define OTTF_BUS DT_PATH(bus)

#define OTTF_IRQ_PERIPH_ENTRY(idx, nodeid) \
  [DT_IRQ_BY_IDX(nodeid, idx, irq)] = DT_DEP_ORD(nodeid),

#define OTTF_IRQ_MATCH_PARENT(idx, child, parent) \
  DT_IRQ_HAS_PARENT_BY_IDX(child, idx, parent)

#define OTTF_IRQ_ENTRY_IF_PARENT(idx, child, parent)     \
  COND_CODE_1(OTTF_IRQ_MATCH_PARENT(idx, child, parent), \
              (OTTF_IRQ_PERIPH_ENTRY(idx, child)), ())

#define OTTF_LISTIFY_IRQS_BY_PARENT(child, parent, fn) \
  LISTIFY(DT_NUM_IRQS(child), fn, (), child, parent)

const ottf_irq_peripheral_t ottf_plic_peripheral_table[kOttfPlicNumIrqs] = {
    [0] = 0,
    DT_FOREACH_CHILD_VARGS(OTTF_BUS, OTTF_LISTIFY_IRQS_BY_PARENT,
                           DT_NODELABEL(rv_plic), OTTF_IRQ_ENTRY_IF_PARENT)};
