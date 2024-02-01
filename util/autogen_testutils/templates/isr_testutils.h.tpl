// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_

${autogen_banner}

/**
 * @file
 * @brief Default ISRs for each IP
 */

#include "sw/device/lib/dif/dif_rv_plic.h"
% for ip in ips_with_difs:
  % if ip.irqs:
    #include "sw/device/lib/dif/dif_${ip.name_snake}.h"
  % endif
% endfor

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h" // Generated.

/**
 * A handle to a PLIC ISR context struct.
 */
typedef struct plic_isr_ctx {
  /**
   * A handle to a rv_plic.
   */
  dif_rv_plic_t *rv_plic;
  /**
   * The HART ID associated with the PLIC (correspond to a PLIC "target").
   */
  uint32_t hart_id;
} plic_isr_ctx_t;

% for ip in ips_with_difs:
  % if ip.irqs:
    /**
     * A handle to a ${ip.name_snake} ISR context struct.
     */
    typedef struct ${ip.name_snake}_isr_ctx {
      /**
       * A handle to a ${ip.name_snake}.
       */
      dif_${ip.name_snake}_t *${ip.name_snake};
      /**
       * The PLIC IRQ ID where this ${ip.name_snake} instance's IRQs start.
       */
      dif_rv_plic_irq_id_t plic_${ip.name_snake}_start_irq_id;
      /**
       * The ${ip.name_snake} IRQ that is expected to be encountered in the ISR.
       */
      dif_${ip.name_snake}_irq_t expected_irq;
      /**
       * Whether or not a single IRQ is expected to be encountered in the ISR.
       */
      bool is_only_irq;
    } ${ip.name_snake}_isr_ctx_t;

  % endif
% endfor

% for ip in ips_with_difs:
  % if ip.irqs:
    /**
     * Services an ${ip.name_snake} IRQ.
     *
     * @param plic_ctx A PLIC ISR context handle.
     * @param ${ip.name_snake}_ctx A(n) ${ip.name_snake} ISR context handle.
    % if ip.has_status_type_irqs():
     * @param mute_status_irq set to true to disable the serviced status type IRQ.
    % endif
     * @param[out] peripheral_serviced Out param for the peripheral that was serviced.
     * @param[out] irq_serviced Out param for the IRQ that was serviced.
     */
    void isr_testutils_${ip.name_snake}_isr(
      plic_isr_ctx_t plic_ctx,
      ${ip.name_snake}_isr_ctx_t ${ip.name_snake}_ctx,
    % if ip.has_status_type_irqs():
      bool mute_status_irq,
    % endif
      top_earlgrey_plic_peripheral_t *peripheral_serviced,
      dif_${ip.name_snake}_irq_t *irq_serviced);

  % endif
% endfor

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_
