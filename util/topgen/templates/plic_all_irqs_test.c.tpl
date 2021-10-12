// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
enabled_peripherals = ['aes', 'alert_handler', 'clkmgr', 'csrng', 'edn',
                       'entropy_src', 'gpio', 'hmac', 'i2c', 'keymgr', 'kmac',
                       'lc_ctrl', 'otbn', 'otp_ctrl', 'pinmux', 'pwrmgr',
                       'rstmgr', 'spi_device', 'sram_ctrl', 'uart', 'usbdev']
parameterized_peripherals = ['alert_handler']

def comment(n):
    return '' if n in enabled_peripherals else '// '
%>\

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
% for n in irq_peripheral_names:
${comment(n)}#include "sw/device/lib/dif/dif_${n}.h"
% endfor
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"
#include "sw/device/tests/plic_all_irqs_test_helper.h"
% for p in parameterized_peripherals:
${comment(p)}#include "${p}_regs.h"  // Generated.
% endfor
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

% for p in helper.irq_peripherals:
${comment(p.name)}static dif_${p.name}_t ${p.inst_name};
% endfor
static dif_rv_plic_t plic;
static const top_earlgrey_plic_target_t kHart = kTopEarlgreyPlicTargetIbex0;

/**
 * Flag indicating which peripheral is under test.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile top_earlgrey_plic_peripheral_t peripheral_expected;

/**
 * Flags indicating the IRQ expected to have triggered and serviced within the
 * peripheral.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
% for n in irq_peripheral_names:
${comment(n)}static volatile dif_${n}_irq_t ${n}_irq_expected;
${comment(n)}static volatile dif_${n}_irq_t ${n}_irq_serviced;
% endfor

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default external IRQ handler in
 * `sw/device/lib/handler.h`.
 */
void handler_irq_external(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
    % for p in helper.irq_peripherals:
    ${comment(p.name)}case ${p.plic_name}:
    ${comment(p.name)}  PERIPHERAL_ISR(${p.name}, ${p.inst_name}, ${p.plic_start_irq});
    ${comment(p.name)}  break;
    % endfor
    default:
      LOG_FATAL("ISR is not implemented!");
      test_status_set(kTestStatusFailed);
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
}

/**
 * Initializes the handles to all peripherals.
 */
static void peripherals_init(void) {
  dif_alert_handler_params_t alert_handler_params = {
    .alert_count = ALERT_HANDLER_PARAM_N_ALERTS,
    .escalation_signal_count = ALERT_HANDLER_PARAM_N_ESC_SEV};

  % for p in helper.irq_peripherals:
  % if p.name in parameterized_peripherals:
  ${comment(p.name)}PERIPHERAL_INIT_WITH_PARAMS(${p.name}, ${p.name}_params, ${p.inst_name}, ${p.base_addr_name});
  % else:
  ${comment(p.name)}PERIPHERAL_INIT(${p.name}, ${p.inst_name}, ${p.base_addr_name});
  % endif
  % endfor

  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  % for p in helper.irq_peripherals:
  ${comment(p.name)}PERIPHERAL_IRQS_CLEAR(${p.inst_name});
  % endfor
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  % for p in helper.irq_peripherals:
  ${comment(p.name)}PERIPHERAL_IRQS_ENABLE(${p.name}, ${p.inst_name});
  % endfor
}

/**
 * Triggers all IRQs in all peripherals one by one.
 *
 * Walks through all instances of all peripherals and triggers an interrupt one
 * by one. Instead of invoking WFI, it waits for a couple of cycles with nops,
 * and then checks if the right interrupt was handled. The ISR which the CPU
 * jumps into checks if the correct interrupt from the right instance triggered.
 */
static void peripheral_irqs_trigger(void) {
  % for p in helper.irq_peripherals:
  ${comment(p.name)}PERIPHERAL_IRQS_TRIGGER(${p.name}, ${p.inst_name}, ${p.plic_name},
  ${comment(p.name)}                        ${p.start_irq}, ${p.end_irq});
  % endfor
}

const test_config_t kTestConfig;

bool test_main(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  peripherals_init();
  rv_plic_testutils_irq_range_enable(&plic, kHart,
      kTopEarlgreyPlicIrqIdNone + 1, kTopEarlgreyPlicIrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}
