// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/**
 * HMAC done 50uS timeout, which should be enough even for a 100kHz device.
 *
 * https://docs.opentitan.org/hw/ip/hmac/doc/
 * Final hash calculation takes 360 cycles, which consists of one
 * block compression and extra HMAC computation.
 */
const uint32_t kHmacEncFinishTimeoutUsec = 50;

/**
 * FIFO empty 10uS timeout, which should be enough even for a 100kHz device.
 *
 * https://docs.opentitan.org/hw/ip/hmac/doc/
 * Single HMAC block compression takes 80 cycles.
 */
const uint32_t kHmacEncEmptyTimeoutUsec = 10;

static plic_isr_ctx_t plic_ctx = {
    .hart_id = kTopEarlgreyPlicTargetIbex0,
};

static dif_hmac_t hmac;
static top_earlgrey_plic_peripheral_t peripheral_serviced;
static dif_hmac_irq_t irq_serviced;
static hmac_isr_ctx_t hmac_ctx = {
    .hmac = &hmac,
    .plic_hmac_start_irq_id = kTopEarlgreyPlicIrqIdHmacHmacDone,
    .is_only_irq = false,
};

OTTF_DEFINE_TEST_CONFIG();

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  isr_testutils_hmac_isr(plic_ctx, hmac_ctx, &peripheral_serviced,
                         &irq_serviced);
}

/**
 * Enables interrupts required by this test.
 */
static void enable_irqs(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, plic_ctx.rv_plic));

  // Enable interrupts in HMAC IP.
  CHECK_DIF_OK(dif_hmac_irq_set_enabled(hmac_ctx.hmac, kDifHmacIrqHmacDone,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(dif_hmac_irq_set_enabled(hmac_ctx.hmac, kDifHmacIrqFifoEmpty,
                                        kDifToggleEnabled));

  // Enable interrupts in PLIC.
  rv_plic_testutils_irq_range_enable(plic_ctx.rv_plic, plic_ctx.hart_id,
                                     kTopEarlgreyPlicIrqIdHmacHmacDone,
                                     kTopEarlgreyPlicIrqIdHmacFifoEmpty);

  // Enable interrupts in Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool test_main(void) {
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  enable_irqs();

  // The purpose of this test is to ensure that HMAC empty and done interrupts
  // assert when the conditions are met. Digest is not verified by this
  // test, which means that a "dummy" data will suffice.
  size_t sent_bytes;
  char data[4] = {0xaa, 0xbb, 0xcc, 0xdd};
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(&hmac, kHmacTransactionConfig));
  hmac_ctx.expected_irq = kDifHmacIrqFifoEmpty;
  CHECK_DIF_OK(
      dif_hmac_fifo_push(&hmac, &data[0], ARRAYSIZE(data), &sent_bytes));
  hmac_testutils_check_message_length(&hmac, 32);

  // Spin waiting for the "empty" interrupt.
  IBEX_SPIN_FOR(irq_serviced == hmac_ctx.expected_irq,
                kHmacEncEmptyTimeoutUsec);

  // Race conditions could result in a stale value due to `hmac_empty_irq`
  // being set in the ISR, however, in practice that does not matter.
  hmac_ctx.expected_irq = kDifHmacIrqHmacDone;
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  LOG_INFO("Waiting for HMAC to finish");

  // Spin waiting for the "done" interrupt.
  IBEX_SPIN_FOR(irq_serviced == hmac_ctx.expected_irq,
                kHmacEncFinishTimeoutUsec);

  // Finish the HMAC operation.
  dif_hmac_digest_t dummy_digest;
  CHECK_DIF_OK(dif_hmac_finish(&hmac, &dummy_digest));

  return true;
}
