// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_plic_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

static const dif_rv_plic_target_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static dif_rv_plic_t plic0;

static uint32_t external_intr_triggered = 0;
static uint32_t software_intr_triggered = 0;

/**
 * Configures all interrupts in PLIC.
 */
static void plic_configure_irqs(dif_rv_plic_t *plic) {
  // Set IRQ priorities to MAX and Enable the IRQ
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    const dif_rv_plic_irq_id_t irq_id = (dif_rv_plic_irq_id_t)i;
    CHECK_DIF_OK(
        dif_rv_plic_irq_set_priority(plic, irq_id, kDifRvPlicMaxPriority));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, irq_id, kPlicTarget,
                                             kDifToggleEnabled));
  }

  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
}

/**
 * External ISR.
 *
 * PLIC interrupt triggers ottf_external_isr() function. The expectation is
 * MSIP triggers this. Inside the routine, it reads all Interrupt Pending bits
 * and confirms only MSIP occurs.
 */
void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t interrupt_id;

  ++external_intr_triggered;
  LOG_FATAL("External Interrupt should not occur");
  test_status_set(kTestStatusFailed);

  // Clean up external ISRs (claim & complete)
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic0, kPlicTarget, &interrupt_id));
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic0, kPlicTarget, interrupt_id));
}

/**
 * Software ISR
 *
 * Only SW ISR should occur in this test.
 */
void ottf_software_isr(void) {
  LOG_INFO("SOFTWARE ISR entered");
  ++software_intr_triggered;

  // Clean up software ISRs (claim? clear?)
  CHECK_DIF_OK(dif_rv_plic_software_irq_acknowledge(&plic0, kPlicTarget));

  LOG_INFO("Software ISR event is cleared");
}

static void execute_test(dif_rv_plic_t *plic) {
  // Force SW IRQ
  CHECK_DIF_OK(dif_rv_plic_software_irq_force(plic, kPlicTarget));

  // Wait SW IRQ being processed
  while (abs_mmio_read32((uint32_t)&software_intr_triggered) == 0) {
    busy_spin_micros(10);
  }
}

bool test_main(void) {
  // Enable IRQs on Ibex
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic0));

  plic_configure_irqs(&plic0);

  // Enable MSIE
  irq_software_ctrl(true);

  execute_test(&plic0);

  // Pass condition
  if ((abs_mmio_read32((uint32_t)&software_intr_triggered) == 1) &&
      (abs_mmio_read32((uint32_t)&external_intr_triggered) == 0)) {
    return true;
  }

  return false;
}
