// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "devicetables.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "sw/device/lib/testing/autogen/isr_testutils.h"

enum {
  kPlicTarget = 0,
};

static const dt_hmac_t *kHmacDt = &kDtHmac[0];

static plic_isr_ctx_t plic_ctx = {
    .hart_id = kPlicTarget,
};

static dif_hmac_irq_t irq_serviced;
static hmac_isr_ctx_t hmac_ctx = {
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
void ottf_external_isr(uint32_t *exc_info) {
  isr_testutils_hmac_isr_try(plic_ctx, hmac_ctx, /* plic_id */ NULL,
                             /* mute_status_irq */ false, &irq_serviced);
}

/**
 * Enables interrupts required by this test.
 */
static void irqs_init(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(&kDtRvPlic[0], plic_ctx.rv_plic));

  // Enable interrupts in HMAC IP.
  CHECK_DIF_OK(dif_hmac_irq_set_enabled(hmac_ctx.hmac, kDifHmacIrqHmacDone,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(dif_hmac_irq_set_enabled(hmac_ctx.hmac, kDifHmacIrqFifoEmpty,
                                        kDifToggleEnabled));

  // Enable interrupts in PLIC.
  rv_plic_testutils_irq_range_enable(
      plic_ctx.rv_plic, plic_ctx.hart_id,
      dt_hmac_irq_to_plic_id(kHmacDt, kDtHmacIrqHmacDone),
      dt_hmac_irq_to_plic_id(kHmacDt, kDtHmacIrqFifoEmpty));
  // Enable interrupts in Ibex.
  irq_external_ctrl(true);
  irq_global_ctrl(true);
}

bool test_main(void) {
  dif_hmac_t hmac;
  dif_rv_plic_t plic;
  plic_ctx.rv_plic = &plic;

  CHECK_DIF_OK(dif_hmac_init_from_dt(kHmacDt, &hmac));
  isr_testutils_hmac_init_from_dt(&hmac_ctx, &hmac, kHmacDt);

  irqs_init();

  // Use HMAC in SHA256 mode to generate a 256bit key from `kHmacRefLongKey`.
  CHECK_DIF_OK(
      dif_hmac_mode_sha256_start(hmac_ctx.hmac, kHmacTransactionConfig));
  CHECK_STATUS_OK(hmac_testutils_push_message(
      hmac_ctx.hmac, (char *)kHmacRefLongKey, sizeof(kHmacRefLongKey)));
  CHECK_STATUS_OK(hmac_testutils_check_message_length(
      hmac_ctx.hmac, sizeof(kHmacRefLongKey) * 8));

  // Expect the done irq after processing data.
  hmac_ctx.expected_irq = kDifHmacIrqHmacDone;
  irq_serviced = UINT32_MAX;

  CHECK_DIF_OK(dif_hmac_process(hmac_ctx.hmac));
  dif_hmac_digest_t key_digest;
  CHECK_STATUS_OK(hmac_testutils_finish_polled(hmac_ctx.hmac, &key_digest));
  CHECK_ARRAYS_EQ(key_digest.digest, kHmacRefExpectedLongKeyDigest.digest,
                  ARRAYSIZE(key_digest.digest));

  CHECK(irq_serviced == hmac_ctx.expected_irq);

  // Generate HMAC final digest, using the resulted SHA256 digest over the
  // `kHmacRefLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(
      hmac_ctx.hmac, (uint8_t *)&key_digest.digest[0], kHmacTransactionConfig));
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac_ctx.hmac, kHmacRefData,
                                              sizeof(kHmacRefData)));
  CHECK_STATUS_OK(hmac_testutils_check_message_length(
      hmac_ctx.hmac, sizeof(kHmacRefData) * 8));
  CHECK_DIF_OK(dif_hmac_process(hmac_ctx.hmac));
  LOG_INFO("Waiting for HMAC pooling to finish");
  return status_ok(hmac_testutils_finish_and_check_polled(
      hmac_ctx.hmac, &kHmacRefExpectedDigest));
}
