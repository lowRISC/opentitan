// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/autogen_testutils.py

#include "sw/top_darjeeling/sw/test/utils/autogen/isr_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/alert_handler/dif/dif_alert_handler.h"
#include "sw/ip/aon_timer/dif/dif_aon_timer.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/dma/dif/dif_dma.h"
#include "sw/ip/edn/dif/dif_edn.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/hmac/dif/dif_hmac.h"
#include "sw/ip/i2c/dif/dif_i2c.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/ip/mbx/dif/dif_mbx.h"
#include "sw/ip/otbn/dif/dif_otbn.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/pwrmgr/dif/dif_pwrmgr.h"
#include "sw/ip/rv_plic/dif/dif_rv_plic.h"
#include "sw/ip/rv_timer/dif/dif_rv_timer.h"
#include "sw/ip/sensor_ctrl/dif/dif_sensor_ctrl.h"
#include "sw/ip/soc_proxy/dif/dif_soc_proxy.h"
#include "sw/ip/socdbg_ctrl/dif/dif_socdbg_ctrl.h"
#include "sw/ip/spi_device/dif/dif_spi_device.h"
#include "sw/ip/spi_host/dif/dif_spi_host.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

void isr_testutils_alert_handler_isr(
    plic_isr_ctx_t plic_ctx, alert_handler_isr_ctx_t alert_handler_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_alert_handler_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_alert_handler_irq_t irq =
      (dif_alert_handler_irq_t)(plic_irq_id -
                                alert_handler_ctx
                                    .plic_alert_handler_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (alert_handler_ctx.is_only_irq) {
    dif_alert_handler_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_alert_handler_irq_get_state(
        alert_handler_ctx.alert_handler, &snapshot));
    CHECK(snapshot == (dif_alert_handler_irq_state_snapshot_t)(1 << irq),
          "Only alert_handler IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_alert_handler_irq_get_type(alert_handler_ctx.alert_handler,
                                              irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(
        alert_handler_ctx.alert_handler, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_aon_timer_isr(
    plic_isr_ctx_t plic_ctx, aon_timer_isr_ctx_t aon_timer_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_aon_timer_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_aon_timer_irq_t irq =
      (dif_aon_timer_irq_t)(plic_irq_id -
                            aon_timer_ctx.plic_aon_timer_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (aon_timer_ctx.is_only_irq) {
    dif_aon_timer_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_aon_timer_irq_get_state(aon_timer_ctx.aon_timer, &snapshot));
    CHECK(snapshot == (dif_aon_timer_irq_state_snapshot_t)(1 << irq),
          "Only aon_timer IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_aon_timer_irq_get_type(aon_timer_ctx.aon_timer, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(aon_timer_ctx.aon_timer, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_csrng_isr(
    plic_isr_ctx_t plic_ctx, csrng_isr_ctx_t csrng_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_csrng_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_csrng_irq_t irq =
      (dif_csrng_irq_t)(plic_irq_id - csrng_ctx.plic_csrng_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (csrng_ctx.is_only_irq) {
    dif_csrng_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_csrng_irq_get_state(csrng_ctx.csrng, &snapshot));
    CHECK(snapshot == (dif_csrng_irq_state_snapshot_t)(1 << irq),
          "Only csrng IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_csrng_irq_get_type(csrng_ctx.csrng, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_csrng_irq_acknowledge(csrng_ctx.csrng, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_dma_isr(
    plic_isr_ctx_t plic_ctx, dma_isr_ctx_t dma_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_dma_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_dma_irq_t irq =
      (dif_dma_irq_t)(plic_irq_id - dma_ctx.plic_dma_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (dma_ctx.is_only_irq) {
    dif_dma_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_dma_irq_get_state(dma_ctx.dma, &snapshot));
    CHECK(snapshot == (dif_dma_irq_state_snapshot_t)(1 << irq),
          "Only dma IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_dma_irq_get_type(dma_ctx.dma, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_dma_irq_acknowledge(dma_ctx.dma, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_edn_isr(
    plic_isr_ctx_t plic_ctx, edn_isr_ctx_t edn_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_edn_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_edn_irq_t irq =
      (dif_edn_irq_t)(plic_irq_id - edn_ctx.plic_edn_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (edn_ctx.is_only_irq) {
    dif_edn_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_edn_irq_get_state(edn_ctx.edn, &snapshot));
    CHECK(snapshot == (dif_edn_irq_state_snapshot_t)(1 << irq),
          "Only edn IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_edn_irq_get_type(edn_ctx.edn, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_edn_irq_acknowledge(edn_ctx.edn, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_gpio_isr(
    plic_isr_ctx_t plic_ctx, gpio_isr_ctx_t gpio_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_gpio_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_gpio_irq_t irq =
      (dif_gpio_irq_t)(plic_irq_id - gpio_ctx.plic_gpio_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (gpio_ctx.is_only_irq) {
    dif_gpio_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_gpio_irq_get_state(gpio_ctx.gpio, &snapshot));
    CHECK(snapshot == (dif_gpio_irq_state_snapshot_t)(1 << irq),
          "Only gpio IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_gpio_irq_get_type(gpio_ctx.gpio, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_gpio_irq_acknowledge(gpio_ctx.gpio, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_hmac_isr(
    plic_isr_ctx_t plic_ctx, hmac_isr_ctx_t hmac_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_hmac_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_hmac_irq_t irq =
      (dif_hmac_irq_t)(plic_irq_id - hmac_ctx.plic_hmac_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (hmac_ctx.is_only_irq) {
    dif_hmac_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_hmac_irq_get_state(hmac_ctx.hmac, &snapshot));
    CHECK(snapshot == (dif_hmac_irq_state_snapshot_t)(1 << irq),
          "Only hmac IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_hmac_irq_get_type(hmac_ctx.hmac, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_hmac_irq_acknowledge(hmac_ctx.hmac, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_i2c_isr(
    plic_isr_ctx_t plic_ctx, i2c_isr_ctx_t i2c_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_i2c_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_i2c_irq_t irq =
      (dif_i2c_irq_t)(plic_irq_id - i2c_ctx.plic_i2c_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (i2c_ctx.is_only_irq) {
    dif_i2c_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_i2c_irq_get_state(i2c_ctx.i2c, &snapshot));
    CHECK(snapshot == (dif_i2c_irq_state_snapshot_t)(1 << irq),
          "Only i2c IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_i2c_irq_get_type(i2c_ctx.i2c, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_i2c_irq_acknowledge(i2c_ctx.i2c, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_keymgr_dpe_isr(
    plic_isr_ctx_t plic_ctx, keymgr_dpe_isr_ctx_t keymgr_dpe_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_keymgr_dpe_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_keymgr_dpe_irq_t irq =
      (dif_keymgr_dpe_irq_t)(plic_irq_id -
                             keymgr_dpe_ctx.plic_keymgr_dpe_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (keymgr_dpe_ctx.is_only_irq) {
    dif_keymgr_dpe_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_keymgr_dpe_irq_get_state(keymgr_dpe_ctx.keymgr_dpe, &snapshot));
    CHECK(snapshot == (dif_keymgr_dpe_irq_state_snapshot_t)(1 << irq),
          "Only keymgr_dpe IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_keymgr_dpe_irq_get_type(keymgr_dpe_ctx.keymgr_dpe, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_keymgr_dpe_irq_acknowledge(keymgr_dpe_ctx.keymgr_dpe, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_kmac_isr(
    plic_isr_ctx_t plic_ctx, kmac_isr_ctx_t kmac_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_kmac_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_kmac_irq_t irq =
      (dif_kmac_irq_t)(plic_irq_id - kmac_ctx.plic_kmac_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (kmac_ctx.is_only_irq) {
    dif_kmac_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_kmac_irq_get_state(kmac_ctx.kmac, &snapshot));
    CHECK(snapshot == (dif_kmac_irq_state_snapshot_t)(1 << irq),
          "Only kmac IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_kmac_irq_get_type(kmac_ctx.kmac, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_kmac_irq_acknowledge(kmac_ctx.kmac, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_mbx_isr(
    plic_isr_ctx_t plic_ctx, mbx_isr_ctx_t mbx_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_mbx_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_mbx_irq_t irq =
      (dif_mbx_irq_t)(plic_irq_id - mbx_ctx.plic_mbx_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (mbx_ctx.is_only_irq) {
    dif_mbx_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_mbx_irq_get_state(mbx_ctx.mbx, &snapshot));
    CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
          "Only mbx IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_mbx_irq_get_type(mbx_ctx.mbx, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_mbx_irq_acknowledge(mbx_ctx.mbx, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_otbn_isr(
    plic_isr_ctx_t plic_ctx, otbn_isr_ctx_t otbn_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_otbn_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_otbn_irq_t irq =
      (dif_otbn_irq_t)(plic_irq_id - otbn_ctx.plic_otbn_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (otbn_ctx.is_only_irq) {
    dif_otbn_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_otbn_irq_get_state(otbn_ctx.otbn, &snapshot));
    CHECK(snapshot == (dif_otbn_irq_state_snapshot_t)(1 << irq),
          "Only otbn IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_otbn_irq_get_type(otbn_ctx.otbn, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_otbn_irq_acknowledge(otbn_ctx.otbn, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_otp_ctrl_isr(
    plic_isr_ctx_t plic_ctx, otp_ctrl_isr_ctx_t otp_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_otp_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_otp_ctrl_irq_t irq =
      (dif_otp_ctrl_irq_t)(plic_irq_id -
                           otp_ctrl_ctx.plic_otp_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (otp_ctrl_ctx.is_only_irq) {
    dif_otp_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_otp_ctrl_irq_get_state(otp_ctrl_ctx.otp_ctrl, &snapshot));
    CHECK(snapshot == (dif_otp_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only otp_ctrl IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_otp_ctrl_irq_get_type(otp_ctrl_ctx.otp_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge(otp_ctrl_ctx.otp_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_pwrmgr_isr(
    plic_isr_ctx_t plic_ctx, pwrmgr_isr_ctx_t pwrmgr_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_pwrmgr_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_pwrmgr_irq_t irq =
      (dif_pwrmgr_irq_t)(plic_irq_id - pwrmgr_ctx.plic_pwrmgr_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (pwrmgr_ctx.is_only_irq) {
    dif_pwrmgr_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_pwrmgr_irq_get_state(pwrmgr_ctx.pwrmgr, &snapshot));
    CHECK(snapshot == (dif_pwrmgr_irq_state_snapshot_t)(1 << irq),
          "Only pwrmgr IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_pwrmgr_irq_get_type(pwrmgr_ctx.pwrmgr, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(pwrmgr_ctx.pwrmgr, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_rv_timer_isr(
    plic_isr_ctx_t plic_ctx, rv_timer_isr_ctx_t rv_timer_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_rv_timer_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_rv_timer_irq_t irq =
      (dif_rv_timer_irq_t)(plic_irq_id -
                           rv_timer_ctx.plic_rv_timer_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (rv_timer_ctx.is_only_irq) {
    dif_rv_timer_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_rv_timer_irq_get_state(rv_timer_ctx.rv_timer,
                                            plic_ctx.hart_id, &snapshot));
    CHECK(snapshot == (dif_rv_timer_irq_state_snapshot_t)(1 << irq),
          "Only rv_timer IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_rv_timer_irq_get_type(rv_timer_ctx.rv_timer, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_rv_timer_irq_acknowledge(rv_timer_ctx.rv_timer, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_sensor_ctrl_isr(
    plic_isr_ctx_t plic_ctx, sensor_ctrl_isr_ctx_t sensor_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_sensor_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_sensor_ctrl_irq_t irq =
      (dif_sensor_ctrl_irq_t)(plic_irq_id -
                              sensor_ctrl_ctx.plic_sensor_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (sensor_ctrl_ctx.is_only_irq) {
    dif_sensor_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_sensor_ctrl_irq_get_state(sensor_ctrl_ctx.sensor_ctrl, &snapshot));
    CHECK(snapshot == (dif_sensor_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only sensor_ctrl IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_sensor_ctrl_irq_get_type(sensor_ctrl_ctx.sensor_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_sensor_ctrl_irq_acknowledge(sensor_ctrl_ctx.sensor_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_soc_proxy_isr(
    plic_isr_ctx_t plic_ctx, soc_proxy_isr_ctx_t soc_proxy_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_soc_proxy_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_soc_proxy_irq_t irq =
      (dif_soc_proxy_irq_t)(plic_irq_id -
                            soc_proxy_ctx.plic_soc_proxy_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (soc_proxy_ctx.is_only_irq) {
    dif_soc_proxy_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_soc_proxy_irq_get_state(soc_proxy_ctx.soc_proxy, &snapshot));
    CHECK(snapshot == (dif_soc_proxy_irq_state_snapshot_t)(1 << irq),
          "Only soc_proxy IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_soc_proxy_irq_get_type(soc_proxy_ctx.soc_proxy, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge(soc_proxy_ctx.soc_proxy, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_soc_proxy_isr(
    plic_isr_ctx_t plic_ctx, soc_proxy_isr_ctx_t soc_proxy_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_soc_proxy_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_soc_proxy_irq_t irq =
      (dif_soc_proxy_irq_t)(plic_irq_id -
                            soc_proxy_ctx.plic_soc_proxy_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (soc_proxy_ctx.is_only_irq) {
    dif_soc_proxy_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_soc_proxy_irq_get_state(soc_proxy_ctx.soc_proxy, &snapshot));
    CHECK(snapshot == (dif_soc_proxy_irq_state_snapshot_t)(1 << irq),
          "Only soc_proxy IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_soc_proxy_irq_get_type(soc_proxy_ctx.soc_proxy, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge(soc_proxy_ctx.soc_proxy, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_socdbg_ctrl_isr(
    plic_isr_ctx_t plic_ctx, socdbg_ctrl_isr_ctx_t socdbg_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_socdbg_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_socdbg_ctrl_irq_t irq =
      (dif_socdbg_ctrl_irq_t)(plic_irq_id -
                              socdbg_ctrl_ctx.plic_socdbg_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (socdbg_ctrl_ctx.is_only_irq) {
    dif_socdbg_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_socdbg_ctrl_irq_get_state(socdbg_ctrl_ctx.socdbg_ctrl, &snapshot));
    CHECK(snapshot == (dif_socdbg_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only socdbg_ctrl IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_socdbg_ctrl_irq_get_type(socdbg_ctrl_ctx.socdbg_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_socdbg_ctrl_irq_acknowledge(socdbg_ctrl_ctx.socdbg_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_spi_device_isr(
    plic_isr_ctx_t plic_ctx, spi_device_isr_ctx_t spi_device_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_spi_device_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_spi_device_irq_t irq =
      (dif_spi_device_irq_t)(plic_irq_id -
                             spi_device_ctx.plic_spi_device_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (spi_device_ctx.is_only_irq) {
    dif_spi_device_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_spi_device_irq_get_state(spi_device_ctx.spi_device, &snapshot));
    CHECK(snapshot == (dif_spi_device_irq_state_snapshot_t)(1 << irq),
          "Only spi_device IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_spi_device_irq_get_type(spi_device_ctx.spi_device, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_spi_device_irq_acknowledge(spi_device_ctx.spi_device, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_spi_host_isr(
    plic_isr_ctx_t plic_ctx, spi_host_isr_ctx_t spi_host_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_spi_host_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_spi_host_irq_t irq =
      (dif_spi_host_irq_t)(plic_irq_id -
                           spi_host_ctx.plic_spi_host_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (spi_host_ctx.is_only_irq) {
    dif_spi_host_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_spi_host_irq_get_state(spi_host_ctx.spi_host, &snapshot));
    CHECK(snapshot == (dif_spi_host_irq_state_snapshot_t)(1 << irq),
          "Only spi_host IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_spi_host_irq_get_type(spi_host_ctx.spi_host, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_spi_host_irq_acknowledge(spi_host_ctx.spi_host, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_uart_isr(
    plic_isr_ctx_t plic_ctx, uart_isr_ctx_t uart_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_uart_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_uart_irq_t irq =
      (dif_uart_irq_t)(plic_irq_id - uart_ctx.plic_uart_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (uart_ctx.is_only_irq) {
    dif_uart_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_uart_irq_get_state(uart_ctx.uart, &snapshot));
    CHECK(snapshot == (dif_uart_irq_state_snapshot_t)(1 << irq),
          "Only uart IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_uart_irq_get_type(uart_ctx.uart, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart_ctx.uart, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}
