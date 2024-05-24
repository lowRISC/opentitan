// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

${autogen_banner}

#include "sw/top_${top['name']}/sw/test/utils/autogen/isr_testutils${plic_suffix}.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/rv_plic${plic_suffix}/dif/dif_rv_plic${plic_suffix}.h"
% for ip in ips_with_difs:
  % if ip.irqs:
    #include "sw/ip/${ip.name_snake}/dif/dif_${ip.name_snake}.h"
  % endif
% endfor
#include "sw/lib/sw/device/arch/device.h"

#include "hw/top_${top['name']}/sw/autogen/top_${top['name']}${addr_space_suffix}.h"

% for ip in ips_with_difs:
  % if ip.irqs:
    void isr_testutils_${ip.name_snake}${plic_suffix}_isr(
      plic${plic_suffix}_isr_ctx_t plic_ctx,
      ${ip.name_snake}${plic_suffix}_isr_ctx_t ${ip.name_snake}_ctx,
      top_${top['name']}_plic${plic_suffix}_peripheral_t *peripheral_serviced,
      dif_${ip.name_snake}_irq_t *irq_serviced) {

      // Claim the IRQ at the PLIC.
      dif_rv_plic${plic_suffix}_irq_id_t plic_irq_id;
      CHECK_DIF_OK(dif_rv_plic${plic_suffix}_irq_claim(
        plic_ctx.rv_plic,
        plic_ctx.hart_id,
        &plic_irq_id));

      // Get the peripheral the IRQ belongs to.
      *peripheral_serviced = (top_${top['name']}_plic${plic_suffix}_peripheral_t)
        top_${top['name']}_plic${plic_suffix}_interrupt_for_peripheral[plic_irq_id];

      // Get the IRQ that was fired from the PLIC IRQ ID.
      dif_${ip.name_snake}_irq_t irq = (dif_${ip.name_snake}_irq_t)(plic_irq_id -
        ${ip.name_snake}_ctx.plic_${ip.name_snake}_start_irq_id);
      *irq_serviced = irq;

      // Check if it is supposed to be the only IRQ fired.
      if (${ip.name_snake}_ctx.is_only_irq) {
        dif_${ip.name_snake}_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_${ip.name_snake}_irq_get_state(
          ${ip.name_snake}_ctx.${ip.name_snake},
        % if ip.name_snake == "rv_timer":
          plic_ctx.hart_id,
        % endif
          &snapshot));
        CHECK(snapshot == (dif_${ip.name_snake}_irq_state_snapshot_t)(1 << irq),
          "Only ${ip.name_snake} IRQ %d expected to fire. Actual IRQ state = %x",
          irq, snapshot);
      }

    % if ip.name_snake == "adc_ctrl":
      // TODO(lowRISC/opentitan:#11354): future releases of the ADC Controller HW should hide
      // the need to also clear the cause CSRs. At which point, this can be removed.
      CHECK_DIF_OK(dif_${ip.name_snake}_irq_clear_causes(
          ${ip.name_snake}_ctx.${ip.name_snake},
          kDifAdcCtrlIrqCauseAll));
    % endif

      // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
      dif_irq_type_t type;
      CHECK_DIF_OK(dif_${ip.name_snake}_irq_get_type(
          ${ip.name_snake}_ctx.${ip.name_snake}, irq, &type));
      if (type == kDifIrqTypeEvent) {
        CHECK_DIF_OK(dif_${ip.name_snake}_irq_acknowledge(
            ${ip.name_snake}_ctx.${ip.name_snake},
            irq));
      }

      // Complete the IRQ at the PLIC.
      CHECK_DIF_OK(dif_rv_plic${plic_suffix}_irq_complete(
          plic_ctx.rv_plic,
          plic_ctx.hart_id,
          plic_irq_id));
    }

  % endif
% endfor
