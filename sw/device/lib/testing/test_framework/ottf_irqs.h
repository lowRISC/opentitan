// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_IRQS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_IRQS_H_

#include <stdint.h>
#include <zephyr/devicetree.h>

typedef uint32_t ottf_irq_peripheral_t;

enum {
  /**
   * Number of IRQ IDs for the PLIC.
   * Note that this is one more than the number of IRQs. The ID of 0 is reserved
   * to indicate no valid interrupt.
   */
  kOttfPlicNumIrqs = DT_PROP(DT_NODELABEL(rv_plic), riscv_ndev),
};

/**
 * A mapping of PLIC IRQ IDs to the dependency ordinal of the peripheral in the
 * device tree. In other words, the values are the same as
 * `DT_DEP_ORD(peripheral_node)`.
 */
extern const ottf_irq_peripheral_t ottf_plic_peripheral_table[kOttfPlicNumIrqs];

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_IRQS_H_
