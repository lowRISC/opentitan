// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off
${gencmd}
<%
import topgen.lib as lib

default_interrupt_domain = lib.get_default_interrupt_domain(top)

irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals[helper.interrupt_domain]})
plic_suffix = "_" + helper.interrupt_domain if helper.interrupt_domain != default_interrupt_domain else ""
plic_suffix_camel = plic_suffix.replace("_", "").capitalize()
plic_name = "rv_plic" + plic_suffix
irq_peripheral_names_with_plic = sorted(irq_peripheral_names + [plic_name])
addr_space_suffix = "_" + helper.addr_space if helper.addr_space != helper.default_addr_space else ""

# For some rv_timer DIFs, tha hart argument follows the instance handle.
def args(p):
    extra_arg = ", kHart" if p.name == "rv_timer" else ""
    return f"&{p.inst_name}{extra_arg}"
%>\
#include <limits.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"
% for n in irq_peripheral_names_with_plic:
#include "sw/ip/${n}/dif/dif_${n}.h"
% endfor
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/irq.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "sw/ip/rv_plic${plic_suffix}/test/utils/rv_plic${plic_suffix}_testutils.h"

#include "hw/top_${top["name"]}/sw/autogen/top_${top["name"]}${addr_space_suffix}.h"

% for p in helper.irq_peripherals[helper.interrupt_domain]:
static dif_${p.name}_t ${p.inst_name};
% endfor
static dif_rv_plic${plic_suffix}_t plic;
static const top_${top["name"]}_plic${plic_suffix}_target_t kHart = kTop${top["name"].capitalize()}Plic${plic_suffix_camel}TargetIbex0;

/**
 * Flag indicating which peripheral is under test.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile top_${top["name"]}_plic${plic_suffix}_peripheral_t peripheral_expected;

/**
 * Flags indicating the IRQ expected to have triggered and serviced within the
 * peripheral.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
% for n in irq_peripheral_names:
static volatile dif_${n}_irq_t ${n}_irq_expected;
static volatile dif_${n}_irq_t ${n}_irq_serviced;
% endfor

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 *
 * For each IRQ, it performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Checks that the index belongs to the expected peripheral.
 * 3. Checks that the correct and the only IRQ from the expected peripheral
 *    triggered.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
void ottf_external_isr(void) {
  dif_rv_plic${plic_suffix}_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic${plic_suffix}_irq_claim(&plic, kHart, &plic_irq_id));

  top_${top["name"]}_plic${plic_suffix}_peripheral_t peripheral = (top_${top["name"]}_plic${plic_suffix}_peripheral_t)
      top_${top["name"]}_plic${plic_suffix}_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
    % for p in helper.irq_peripherals[helper.interrupt_domain]:
    case ${p.plic_name}: {
      dif_${p.name}_irq_t irq = (dif_${p.name}_irq_t)(
          plic_irq_id -
          (dif_rv_plic${plic_suffix}_irq_id_t)${p.plic_start_irq});
      CHECK(irq == ${p.name}_irq_expected,
            "Incorrect ${p.inst_name} IRQ triggered: exp = %d, obs = %d",
            ${p.name}_irq_expected, irq);
      ${p.name}_irq_serviced = irq;

      dif_${p.name}_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_${p.name}_irq_get_state(${args(p)}, &snapshot));
      CHECK(snapshot == (dif_${p.name}_irq_state_snapshot_t)(1 << irq),
            "Only ${p.inst_name} IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_${p.name}_irq_force(&${p.inst_name}, irq, false));
      CHECK_DIF_OK(dif_${p.name}_irq_acknowledge(&${p.inst_name}, irq));
      break;
    }

    % endfor
    default:
      LOG_FATAL("ISR is not implemented!");
      test_status_set(kTestStatusFailed);
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic${plic_suffix}_irq_complete(&plic, kHart, plic_irq_id));
}

/**
 * Initializes the handles to all peripherals.
 */
static void peripherals_init(void) {
  mmio_region_t base_addr;

  % for p in helper.irq_peripherals[helper.interrupt_domain]:
  base_addr = mmio_region_from_addr(${p.base_addr_name});
  CHECK_DIF_OK(dif_${p.name}_init(base_addr, &${p.inst_name}));

  % endfor
  base_addr = mmio_region_from_addr(TOP_${top["name"].upper()}_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic${plic_suffix}_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  % for p in helper.irq_peripherals[helper.interrupt_domain]:
  CHECK_DIF_OK(dif_${p.name}_irq_acknowledge_all(${args(p)}));
  % endfor
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  % for n in irq_peripheral_names:
<%
  if n == "aon_timer": continue
%>\
  dif_${n}_irq_state_snapshot_t ${n}_irqs =
      (dif_${n}_irq_state_snapshot_t)UINT_MAX;
  % endfor

  % for p in helper.irq_peripherals[helper.interrupt_domain]:
<%
  if p.name == "aon_timer": continue
%>\
<%
  indent = ""
%>\
  % if p.inst_name == "uart0":
<%
  indent = "  "
%>\
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
  % endif
  ${indent}CHECK_DIF_OK(
  ${indent}    dif_${p.name}_irq_restore_all(${args(p)}, &${p.name}_irqs));
  % if p.inst_name == "uart0":
  }
  % endif
  % endfor
}

/**
 * Triggers all IRQs in all peripherals one by one.
 *
 * Walks through all instances of all peripherals and triggers an interrupt one
 * by one, by forcing with the `intr_test` CSR. On trigger, the CPU instantly
 * jumps into the ISR. The main flow of execution thus proceeds to check that
 * the correct IRQ was serviced immediately. The ISR, in turn checks if the
 * expected IRQ from the expected peripheral triggered.
 */
static void peripheral_irqs_trigger(void) {
  % for p in helper.irq_peripherals[helper.interrupt_domain]:
<%
  indent = ""
%>\
  % if p.inst_name == "uart0":
<%
  indent = "  "
%>\
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
  % endif
  ${indent}peripheral_expected = ${p.plic_name};
  ${indent}for (dif_${p.name}_irq_t irq = ${p.start_irq};
  ${indent}     irq <= ${p.end_irq}; ++irq) {
  ${indent}  ${p.name}_irq_expected = irq;
  ${indent}  LOG_INFO("Triggering ${p.inst_name} IRQ %d.", irq);
  ${indent}  CHECK_DIF_OK(dif_${p.name}_irq_force(&${p.inst_name}, irq, true));

  ${indent}  // This avoids a race where *irq_serviced is read before
  ${indent}  // entering the ISR.
  ${indent}  IBEX_SPIN_FOR(${p.name}_irq_serviced == irq, 1);
  ${indent}  LOG_INFO("IRQ %d from ${p.inst_name} is serviced.", irq);
  ${indent}}
  % if p.inst_name == "uart0":
  }
  % endif
${"" if loop.last else "\n"}\
  % endfor
}

/**
 * Checks that the target ID corresponds to the ID of the hart on which
 * this test is executed on. This check is meant to be used in a
 * single-hart system only.
 */
static void check_hart_id(uint32_t exp_hart_id) {
  uint32_t act_hart_id;
  CSR_READ(CSR_REG_MHARTID, &act_hart_id);
  CHECK(act_hart_id == exp_hart_id, "Processor has unexpected HART ID.");
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  peripherals_init();
  check_hart_id((uint32_t)kHart);
  rv_plic${plic_suffix}_testutils_irq_range_enable(
      &plic, kHart, kTop${top["name"].capitalize()}Plic${plic_suffix_camel}IrqIdNone + 1, kTop${top["name"].capitalize()}Plic${plic_suffix_camel}IrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}

// clang-format on
