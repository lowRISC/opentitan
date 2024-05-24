// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_TOP_${top['name'].upper()}_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS${plic_suffix.upper()}_H_
#define OPENTITAN_SW_TOP_${top['name'].upper()}_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS${plic_suffix.upper()}_H_

${autogen_banner}

/**
 * @file
 * @brief Default ISRs for each IP
 */

#include "sw/ip/rv_plic${plic_suffix}/dif/dif_rv_plic${plic_suffix}.h"
% for ip in ips_with_difs:
  % if ip.irqs:
    #include "sw/ip/${ip.name_snake}/dif/dif_${ip.name_snake}.h"
  % endif
% endfor
#include "sw/lib/sw/device/arch/device.h"

#include "hw/top_${top['name']}/sw/autogen/top_${top['name']}.h"

/**
 * A handle to a PLIC ISR context struct.
 */
typedef struct plic${plic_suffix}_isr_ctx {
  /**
   * A handle to a rv_plic.
   */
  dif_rv_plic${plic_suffix}_t *rv_plic;
  /**
   * The HART ID associated with the PLIC (correspond to a PLIC "target").
   */
  uint32_t hart_id;
} plic${plic_suffix}_isr_ctx_t;

% for ip in ips_with_difs:
  % if ip.irqs:
    /**
     * A handle to a ${ip.name_snake} ISR context struct.
     */
    typedef struct ${ip.name_snake}${plic_suffix}_isr_ctx {
      /**
       * A handle to a ${ip.name_snake}.
       */
      dif_${ip.name_snake}_t *${ip.name_snake};
      /**
       * The PLIC IRQ ID where this ${ip.name_snake} instance's IRQs start.
       */
      dif_rv_plic${plic_suffix}_irq_id_t plic_${ip.name_snake}_start_irq_id;
      /**
       * The ${ip.name_snake} IRQ that is expected to be encountered in the ISR.
       */
      dif_${ip.name_snake}_irq_t expected_irq;
      /**
       * Whether or not a single IRQ is expected to be encountered in the ISR.
       */
      bool is_only_irq;
    } ${ip.name_snake}${plic_suffix}_isr_ctx_t;

  % endif
% endfor

% for ip in ips_with_difs:
  % if ip.irqs:
    /**
     * Services an ${ip.name_snake} IRQ.
     *
     * @param plic_ctx A PLIC ISR context handle.
     * @param ${ip.name_snake}_ctx A(n) ${ip.name_snake} ISR context handle.
     * @param[out] peripheral_serviced Out param for the peripheral that was serviced.
     * @param[out] irq_serviced Out param for the IRQ that was serviced.
     */
    void isr_testutils_${ip.name_snake}${plic_suffix}_isr(
      plic${plic_suffix}_isr_ctx_t plic_ctx,
      ${ip.name_snake}${plic_suffix}_isr_ctx_t ${ip.name_snake}${plic_suffix}_ctx,
      top_${top['name']}_plic${plic_suffix}_peripheral_t *peripheral_serviced,
      dif_${ip.name_snake}_irq_t *irq_serviced);

  % endif
% endfor

#endif  // OPENTITAN_SW_TOP_${top['name'].upper()}_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS${plic_suffix.upper()}_H_
