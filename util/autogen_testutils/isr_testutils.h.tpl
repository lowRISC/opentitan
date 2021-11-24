// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

${autogen_banner}

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_

% for ip in ips_with_difs:
  % if ip.irqs:
  /* 
   * Services an ${ip.name_snake} IRQ at the IP that raised it, and verifies this
   * matches the IRQ that was raised at the PLIC.
   *  
   * @param ${ip.name_snake} A(n) ${ip.name_snake} DIF handle. 
   * @param plic_irq_id The triggered PLIC IRQ ID. 
   * @param plic_${ip.name_snake}_start_irq_id The PLIC IRQ ID where ${ip.name_snake} starts. 
   * @param expected_${ip.name_snake}_irq The expected ${ip.name_snake} IRQ. 
   * @param is_only_irq This is the only IRQ expected to be raised.
   */
  void isr_testutils_${ip.name_snake}(dif_${ip.name_snake}_t *${ip.name_snake}, 
                                      dif_rv_plic_irq_id_t plic_irq_id, 
                                      dif_rv_plic_irq_id_t plic_${ip.name_snake}_start_irq_id, 
                                      dif_${ip.name_snake}_irq_id_t expected_${ip.name_snake}_irq,
                                      bool is_only_irq);

  % endif
% endfor

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AUTOGEN_ISR_TESTUTILS_H_
