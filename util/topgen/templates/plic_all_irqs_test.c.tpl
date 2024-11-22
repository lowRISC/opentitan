// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off
${gencmd}
<%
## Get unique module names (not instance names) and the associated masks
## determining interrupt type and default behavior. The helper list is
## already sorted, so no need to sort it again here.
known_names = {}
irq_peripheral_names = []
status_default_masks = []
status_type_masks = []
for p in helper.irq_peripherals:
  if p.name not in known_names:
    known_names.update({p.name: 1})
    irq_peripheral_names.append(p.name)
    status_default_masks.append(p.status_default_mask)
    status_type_masks.append(p.status_type_mask)

# For some rv_timer DIFs, tha hart argument follows the instance handle.
def args(p):
    extra_arg = ", kHart" if p.name == "rv_timer" else ""
    return f"&{p.inst_name}{extra_arg}"
%>\
#include <limits.h>

// This test should avoid otp_ctrl interrupts in rom_ext, since the rom
// extension configures CSR accesses to OTP and AST to become illegal.
//
// This test is getting too big so we need to split it up. To do so,
// each peripheral is given an ID (according to their alphabetical order)
// and we define TEST_MIN_IRQ_PERIPHERAL and TEST_MAX_IRQ_PERIPHERAL to
// choose which ones are being tested.

#ifndef TEST_MIN_IRQ_PERIPHERAL
#define TEST_MIN_IRQ_PERIPHERAL 0
#endif

#ifndef TEST_MAX_IRQ_PERIPHERAL
#define TEST_MAX_IRQ_PERIPHERAL ${len(irq_peripheral_names)}
#endif

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/mmio.h"
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
#include "sw/device/lib/dif/dif_${n}.h"
% endfor
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_${top["name"]}/sw/autogen/top_${top["name"]}.h"

% for p in helper.irq_peripherals:
<%
  i = irq_peripheral_names.index(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
static dif_${p.name}_t ${p.inst_name};
#endif

% endfor
static dif_rv_plic_t plic;
static const top_${top["name"]}_plic_target_t kHart = kTop${top["name"].capitalize()}PlicTargetIbex0;

/**
 * Flag indicating which peripheral is under test.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile top_${top["name"]}_plic_peripheral_t peripheral_expected;

/**
 * Flags indicating the IRQ expected to have triggered and serviced within the
 * peripheral.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */

% for i, n in enumerate(irq_peripheral_names):
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_${n}_irq_t ${n}_irq_expected;
static volatile dif_${n}_irq_t ${n}_irq_serviced;
#endif

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
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  top_${top["name"]}_plic_peripheral_t peripheral = (top_${top["name"]}_plic_peripheral_t)
      top_${top["name"]}_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
% for p in helper.irq_peripherals:
<%
  i = irq_peripheral_names.index(p.name)
  indent = " " * len(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
    case ${p.plic_name}: {
      dif_${p.name}_irq_t irq =
          (dif_${p.name}_irq_t)(plic_irq_id -
${indent}                       (dif_rv_plic_irq_id_t)
${indent}                           ${p.plic_start_irq});
      CHECK(irq == ${p.name}_irq_expected,
            "Incorrect ${p.inst_name} IRQ triggered: exp = %d, obs = %d",
            ${p.name}_irq_expected, irq);
      ${p.name}_irq_serviced = irq;

      dif_${p.name}_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_${p.name}_irq_get_state(${args(p)}, &snapshot));
  ## In case we have status type interrupts that are asserted by default,
  ## we have to account for them in this check.
  % if p.status_default_mask != 0:
      CHECK(snapshot == (dif_${p.name}_irq_state_snapshot_t)((1 << irq) | ${"0x{:x}".format(p.status_default_mask)}),
            "Expected ${p.inst_name} interrupt status %x. Actual interrupt "
            "status = %x",
            (1 << irq) | ${"0x{:x}".format(p.status_default_mask)}, snapshot);
  % else:
      CHECK(snapshot == (dif_${p.name}_irq_state_snapshot_t)(1 << irq),
            "Only ${p.inst_name} IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);
  % endif

  % if p.status_type_mask != 0:
      if (${"0x{:x}".format(p.status_type_mask)} & (1 << irq)) {
        // We do not acknowledge status type interrupt at the IP side, but we
        // need to clear the test force register.
        CHECK_DIF_OK(dif_${p.name}_irq_force(&${p.inst_name}, irq, false));
        // In case this status interrupt is asserted by default, we also
        // disable it at this point so that it does not interfere with the
        // rest of the test.
        if ((${"0x{:x}".format(p.status_default_mask)} & (1 << irq))) {
          CHECK_DIF_OK(dif_${p.name}_irq_set_enabled(&${p.inst_name}, irq, false));
        }
      } else {
        // We acknowledge event type interrupt.
        CHECK_DIF_OK(dif_${p.name}_irq_acknowledge(&${p.inst_name}, irq));
      }
  % else:
      CHECK_DIF_OK(dif_${p.name}_irq_acknowledge(&${p.inst_name}, irq));
  % endif
      break;
    }
#endif

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
  mmio_region_t base_addr;

  % for p in helper.irq_peripherals:
<%
  i = irq_peripheral_names.index(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(${p.base_addr_name});
  CHECK_DIF_OK(dif_${p.name}_init(base_addr, &${p.inst_name}));
#endif

  % endfor
  base_addr = mmio_region_from_addr(TOP_${top["name"].upper()}_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  % for p in helper.irq_peripherals:
<%
  indent = ""
  i = irq_peripheral_names.index(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
  % if p.inst_name == "otp_ctrl":
<%
  indent = "  "
%>\
  if (kBootStage != kBootStageOwner) {
  % endif
  ${indent}CHECK_DIF_OK(dif_${p.name}_irq_acknowledge_all(${args(p)}));
  % if p.inst_name == "otp_ctrl":
  }
  % endif
#endif
${"" if loop.last else "\n"}\
  % endfor
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  % for i, n in enumerate(irq_peripheral_names):
<%
  if n == "aon_timer": continue
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
% if status_default_masks[i] != 0:
  // Note: this peripheral contains status interrupts that are asserted by
  // default. Therefore, not all interrupts are enabled here, since that
  // would interfere with this test. Instead, these interrupts are enabled on
  // demand once they are being tested.
% endif
  dif_${n}_irq_state_snapshot_t ${n}_irqs =
      (dif_${n}_irq_state_snapshot_t)${"0x{:x}".format(0xFFFFFFFF & ~status_default_masks[i])};
#endif

  % endfor
  % for p in helper.irq_peripherals:
<%
  if p.name == "aon_timer": continue
  i = irq_peripheral_names.index(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
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
  % if p.inst_name == "otp_ctrl":
<%
  indent = "  "
%>\
  if (kBootStage != kBootStageOwner) {
  % endif
  ${indent}CHECK_DIF_OK(dif_${p.name}_irq_restore_all(${args(p)}, &${p.name}_irqs));
  % if p.inst_name == "uart0" or p.inst_name == "otp_ctrl":
  }
  % endif
#endif
${"" if loop.last else "\n"}\
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
  unsigned int status_default_mask;
  // Depending on the build configuration, this variable may show up as unused
  // in the clang linter. This statement waives that error.
  (void)status_default_mask;

  % for p in helper.irq_peripherals:
<%
  i = irq_peripheral_names.index(p.name)
%>\
#if TEST_MIN_IRQ_PERIPHERAL <= ${i} && ${i} < TEST_MAX_IRQ_PERIPHERAL
<%
  indent = ""
%>\
  % if p.inst_name == "uart0" or p.name == "aon_timer":
<%
  indent = "  "
%>\
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  // aon_timer may generate a NMI instead of a PLIC IRQ depending on the ROM.
  // Since there are other tests covering this already, we just skip this for
  // non-DV setups.
  if (kDeviceType == kDeviceSimDV) {
  % endif
  % if p.inst_name == "otp_ctrl":
<%
  indent = "  "
%>\
  // Skip OTP_CTRL in boot stage owner since ROM_EXT configures all accesses
  // to OTP_CTRL and AST to be illegal.
  if (kBootStage != kBootStageOwner) {
  % endif
  ${indent}peripheral_expected = ${p.plic_name};
% if p.status_type_mask != 0:
  ${indent}status_default_mask = ${"0x{:x}".format(p.status_default_mask)};
% endif
  ${indent}for (dif_${p.name}_irq_t irq = ${p.start_irq}; irq <= ${p.end_irq};
  ${indent}     ++irq) {
  ${indent}  ${p.name}_irq_expected = irq;
  ${indent}  LOG_INFO("Triggering ${p.inst_name} IRQ %d.", irq);
  ${indent}  CHECK_DIF_OK(dif_${p.name}_irq_force(&${p.inst_name}, irq, true));

% if p.status_type_mask != 0:
  ${indent}  // In this case, the interrupt has not been enabled yet because that would
  ${indent}  // interfere with testing other interrupts. We enable it here and let the
  ${indent}  // interrupt handler disable it again.
  ${indent}  if ((status_default_mask & 0x1)) {
  ${indent}    CHECK_DIF_OK(dif_${p.name}_irq_set_enabled(&${p.inst_name}, irq, true));
  ${indent}  }
  ${indent}  status_default_mask >>= 1;

% endif
  ${indent}  // This avoids a race where *irq_serviced is read before
  ${indent}  // entering the ISR.
  ${indent}  IBEX_SPIN_FOR(${p.name}_irq_serviced == irq, 1);
  ${indent}  LOG_INFO("IRQ %d from ${p.inst_name} is serviced.", irq);
  ${indent}}
  % if p.inst_name == "uart0" or p.name == "aon_timer" or p.name == "otp_ctrl":
  }
  % endif
#endif
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
  rv_plic_testutils_irq_range_enable(
      &plic, kHart, kTop${top["name"].capitalize()}PlicIrqIdNone + 1, kTop${top["name"].capitalize()}PlicIrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}

// clang-format on
