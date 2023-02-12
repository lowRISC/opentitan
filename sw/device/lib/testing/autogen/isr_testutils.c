// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/autogen_testutils.py

#include "sw/device/lib/testing/autogen/isr_testutils.h"

#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

void isr_testutils_adc_ctrl_isr(
    plic_isr_ctx_t plic_ctx, adc_ctrl_isr_ctx_t adc_ctrl_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_adc_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_adc_ctrl_irq_t irq =
      (dif_adc_ctrl_irq_t)(plic_irq_id -
                           adc_ctrl_ctx.plic_adc_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (adc_ctrl_ctx.is_only_irq) {
    dif_adc_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_adc_ctrl_irq_get_state(adc_ctrl_ctx.adc_ctrl, &snapshot));
    CHECK(snapshot == (dif_adc_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only adc_ctrl IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // TODO(lowRISC/opentitan:#11354): future releases of the ADC Controller HW
  // should hide the need to also clear the cause CSRs. At which point, this can
  // be removed.
  CHECK_DIF_OK(dif_adc_ctrl_irq_clear_causes(adc_ctrl_ctx.adc_ctrl,
                                             kDifAdcCtrlIrqCauseAll));

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_adc_ctrl_irq_get_type(adc_ctrl_ctx.adc_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_adc_ctrl_irq_acknowledge(adc_ctrl_ctx.adc_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_alert_handler_isr(
    plic_isr_ctx_t plic_ctx, alert_handler_isr_ctx_t alert_handler_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_alert_handler_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_aon_timer_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_csrng_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_edn_isr(plic_isr_ctx_t plic_ctx, edn_isr_ctx_t edn_ctx,
                           top_earlgrey_plic_peripheral_t *peripheral_serviced,
                           dif_edn_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_entropy_src_isr(
    plic_isr_ctx_t plic_ctx, entropy_src_isr_ctx_t entropy_src_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_entropy_src_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_entropy_src_irq_t irq =
      (dif_entropy_src_irq_t)(plic_irq_id -
                              entropy_src_ctx.plic_entropy_src_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (entropy_src_ctx.is_only_irq) {
    dif_entropy_src_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_entropy_src_irq_get_state(entropy_src_ctx.entropy_src, &snapshot));
    CHECK(snapshot == (dif_entropy_src_irq_state_snapshot_t)(1 << irq),
          "Only entropy_src IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_entropy_src_irq_get_type(entropy_src_ctx.entropy_src, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_entropy_src_irq_acknowledge(entropy_src_ctx.entropy_src, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_flash_ctrl_isr(
    plic_isr_ctx_t plic_ctx, flash_ctrl_isr_ctx_t flash_ctrl_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_flash_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_flash_ctrl_irq_t irq =
      (dif_flash_ctrl_irq_t)(plic_irq_id -
                             flash_ctrl_ctx.plic_flash_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (flash_ctrl_ctx.is_only_irq) {
    dif_flash_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_flash_ctrl_irq_get_state(flash_ctrl_ctx.flash_ctrl, &snapshot));
    CHECK(snapshot == (dif_flash_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only flash_ctrl IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_flash_ctrl_irq_get_type(flash_ctrl_ctx.flash_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_flash_ctrl_irq_acknowledge(flash_ctrl_ctx.flash_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_gpio_isr(plic_isr_ctx_t plic_ctx, gpio_isr_ctx_t gpio_ctx,
                            top_earlgrey_plic_peripheral_t *peripheral_serviced,
                            dif_gpio_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_hmac_isr(plic_isr_ctx_t plic_ctx, hmac_isr_ctx_t hmac_ctx,
                            top_earlgrey_plic_peripheral_t *peripheral_serviced,
                            dif_hmac_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_i2c_isr(plic_isr_ctx_t plic_ctx, i2c_isr_ctx_t i2c_ctx,
                           top_earlgrey_plic_peripheral_t *peripheral_serviced,
                           dif_i2c_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_keymgr_isr(
    plic_isr_ctx_t plic_ctx, keymgr_isr_ctx_t keymgr_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_keymgr_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_keymgr_irq_t irq =
      (dif_keymgr_irq_t)(plic_irq_id - keymgr_ctx.plic_keymgr_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (keymgr_ctx.is_only_irq) {
    dif_keymgr_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_keymgr_irq_get_state(keymgr_ctx.keymgr, &snapshot));
    CHECK(snapshot == (dif_keymgr_irq_state_snapshot_t)(1 << irq),
          "Only keymgr IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_keymgr_irq_get_type(keymgr_ctx.keymgr, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_keymgr_irq_acknowledge(keymgr_ctx.keymgr, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_kmac_isr(plic_isr_ctx_t plic_ctx, kmac_isr_ctx_t kmac_ctx,
                            top_earlgrey_plic_peripheral_t *peripheral_serviced,
                            dif_kmac_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_otbn_isr(plic_isr_ctx_t plic_ctx, otbn_isr_ctx_t otbn_ctx,
                            top_earlgrey_plic_peripheral_t *peripheral_serviced,
                            dif_otbn_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_otp_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_pattgen_isr(
    plic_isr_ctx_t plic_ctx, pattgen_isr_ctx_t pattgen_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_pattgen_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_pattgen_irq_t irq =
      (dif_pattgen_irq_t)(plic_irq_id - pattgen_ctx.plic_pattgen_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (pattgen_ctx.is_only_irq) {
    dif_pattgen_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_pattgen_irq_get_state(pattgen_ctx.pattgen, &snapshot));
    CHECK(snapshot == (dif_pattgen_irq_state_snapshot_t)(1 << irq),
          "Only pattgen IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_pattgen_irq_get_type(pattgen_ctx.pattgen, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_pattgen_irq_acknowledge(pattgen_ctx.pattgen, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_pwrmgr_isr(
    plic_isr_ctx_t plic_ctx, pwrmgr_isr_ctx_t pwrmgr_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_pwrmgr_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_rv_timer_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_sensor_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_spi_device_isr(
    plic_isr_ctx_t plic_ctx, spi_device_isr_ctx_t spi_device_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_spi_device_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_spi_host_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_sysrst_ctrl_isr(
    plic_isr_ctx_t plic_ctx, sysrst_ctrl_isr_ctx_t sysrst_ctrl_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_sysrst_ctrl_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_sysrst_ctrl_irq_t irq =
      (dif_sysrst_ctrl_irq_t)(plic_irq_id -
                              sysrst_ctrl_ctx.plic_sysrst_ctrl_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (sysrst_ctrl_ctx.is_only_irq) {
    dif_sysrst_ctrl_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(
        dif_sysrst_ctrl_irq_get_state(sysrst_ctrl_ctx.sysrst_ctrl, &snapshot));
    CHECK(snapshot == (dif_sysrst_ctrl_irq_state_snapshot_t)(1 << irq),
          "Only sysrst_ctrl IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_sysrst_ctrl_irq_get_type(sysrst_ctrl_ctx.sysrst_ctrl, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_sysrst_ctrl_irq_acknowledge(sysrst_ctrl_ctx.sysrst_ctrl, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}

void isr_testutils_uart_isr(plic_isr_ctx_t plic_ctx, uart_isr_ctx_t uart_ctx,
                            top_earlgrey_plic_peripheral_t *peripheral_serviced,
                            dif_uart_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

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

void isr_testutils_usbdev_isr(
    plic_isr_ctx_t plic_ctx, usbdev_isr_ctx_t usbdev_ctx,
    top_earlgrey_plic_peripheral_t *peripheral_serviced,
    dif_usbdev_irq_t *irq_serviced) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(plic_ctx.rv_plic, plic_ctx.hart_id, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  *peripheral_serviced = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID.
  dif_usbdev_irq_t irq =
      (dif_usbdev_irq_t)(plic_irq_id - usbdev_ctx.plic_usbdev_start_irq_id);
  *irq_serviced = irq;

  // Check if it is supposed to be the only IRQ fired.
  if (usbdev_ctx.is_only_irq) {
    dif_usbdev_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_usbdev_irq_get_state(usbdev_ctx.usbdev, &snapshot));
    CHECK(snapshot == (dif_usbdev_irq_state_snapshot_t)(1 << irq),
          "Only usbdev IRQ %d expected to fire. Actual IRQ state = %x", irq,
          snapshot);
  }

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(dif_usbdev_irq_get_type(usbdev_ctx.usbdev, irq, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_usbdev_irq_acknowledge(usbdev_ctx.usbdev, irq));
  }

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        plic_irq_id));
}
