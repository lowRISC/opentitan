// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_hmac.h"     // Generated
#include "dt/dt_rv_plic.h"  // Generated
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static const uint32_t kPlicTarget = 0;
static dif_rv_plic_t rv_plic;
static dt_rv_plic_t kRvPlicDt = kDtRvPlic;
static dif_hmac_t hmac;
static dt_hmac_t kHmacDt = (dt_hmac_t)0;
static_assert(kDtHmacCount >= 1,
              "This test requires at least one HMAC instance");

static volatile dt_hmac_irq_t irq_serviced;

OTTF_DEFINE_TEST_CONFIG();

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

/**
 * Catch HMAC IRQs so they can be checked by the test body.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_hmac_instance_id(kHmacDt)) {
    irq_serviced = dt_hmac_irq_from_plic_id(kHmacDt, irq_id);

    // Acknowledge the IRQ at the peripheral if the IRQ is of the event type.
    dif_irq_type_t type;
    CHECK_DIF_OK(dif_hmac_irq_get_type(&hmac, irq_serviced, &type));
    if (type == kDifIrqTypeEvent) {
      CHECK_DIF_OK(dif_hmac_irq_acknowledge(&hmac, irq_serviced));
    }

    return true;
  }
  return false;
}

/**
 * Enables interrupts required by this test.
 */
static void irqs_init(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  // Enable interrupts in HMAC IP.
  CHECK_DIF_OK(
      dif_hmac_irq_set_enabled(&hmac, kDtHmacIrqHmacDone, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_hmac_irq_set_enabled(&hmac, kDtHmacIrqFifoEmpty, kDifToggleEnabled));

  // Enable interrupts in PLIC.
  rv_plic_testutils_irq_range_enable(
      &rv_plic, kPlicTarget,
      dt_hmac_irq_to_plic_id(kHmacDt, kDtHmacIrqHmacDone),
      dt_hmac_irq_to_plic_id(kHmacDt, kDtHmacIrqFifoEmpty));
  // Enable interrupts in Ibex.
  irq_external_ctrl(true);
  irq_global_ctrl(true);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_hmac_init_from_dt(kHmacDt, &hmac));

  irqs_init();

  // Use HMAC in SHA256 mode to generate a 256bit key from `kHmacRefLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(&hmac, kHmacTransactionConfig));
  CHECK_STATUS_OK(hmac_testutils_push_message(&hmac, (char *)kHmacRefLongKey,
                                              sizeof(kHmacRefLongKey)));
  CHECK_STATUS_OK(
      hmac_testutils_check_message_length(&hmac, sizeof(kHmacRefLongKey) * 8));

  // Expect the done irq after processing data.
  dt_hmac_irq_t expected_irq = kDtHmacIrqHmacDone;
  irq_serviced = UINT32_MAX;

  CHECK_DIF_OK(dif_hmac_process(&hmac));
  dif_hmac_digest_t key_digest;
  CHECK_STATUS_OK(hmac_testutils_finish_polled(&hmac, &key_digest));
  CHECK_ARRAYS_EQ(key_digest.digest, kHmacRefExpectedLongKeyDigest.digest,
                  ARRAYSIZE(key_digest.digest));

  CHECK(irq_serviced == expected_irq);

  // Generate HMAC final digest, using the resulted SHA256 digest over the
  // `kHmacRefLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, (uint8_t *)&key_digest.digest[0],
                                        kHmacTransactionConfig));
  CHECK_STATUS_OK(
      hmac_testutils_push_message(&hmac, kHmacRefData, sizeof(kHmacRefData)));
  CHECK_STATUS_OK(
      hmac_testutils_check_message_length(&hmac, sizeof(kHmacRefData) * 8));
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  LOG_INFO("Waiting for HMAC pooling to finish");
  return status_ok(
      hmac_testutils_finish_and_check_polled(&hmac, &kHmacRefExpectedDigest));
}
