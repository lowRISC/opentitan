// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/gpio.h"
#include "sw/device/lib/testing/json/pinmux_config.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
static dif_uart_t uart0;
static dif_rv_plic_t plic;
static const uint32_t kExpected_intr[] = {17, 18, 19, 20, 21,
                                          22, 25, 26, 27, 28};
static uint32_t intr_index = 0;

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandGpioSet:
        RESP_ERR(uj, gpio_set(uj, &gpio));
        break;
      case kTestCommandGpioGet:
        RESP_ERR(uj, gpio_get(uj, &gpio));
        break;
      case kTestCommandPinmuxConfig:
        RESP_ERR(uj, pinmux_config(uj, &pinmux));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  // We should never reach here.
  return INTERNAL();
}

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 */

void ottf_external_isr(uint32_t *exc_info) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &plic_irq_id));
  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Hyper debug tests get uart interrupt by design.
  // Filter uart interrupt.
  if (peripheral == kTopEarlgreyPlicPeripheralUart0) {
    // Complete the IRQ at PLIC.
    CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                                          plic_irq_id));
    return;
  }

  // For each test, interrupt triggers in order.
  // Once all interrupts are triggered, `intr_index` will be set to 0 for the
  // next test.
  if (peripheral == kTopEarlgreyPlicPeripheralGpio) {
    // Correlate the interrupt fired from GPIO.
    uint32_t gpio_pin_irq_fired = plic_irq_id - kTopEarlgreyPlicIrqIdGpioGpio0;
    CHECK(gpio_pin_irq_fired == kExpected_intr[intr_index],
          "Unexpected interrupt rcv:%d  exp:%d", gpio_pin_irq_fired,
          kExpected_intr[intr_index]);
    intr_index += 1;
    if (intr_index == ARRAYSIZE(kExpected_intr)) {
      intr_index = 0;
      LOG_INFO("index back to 0");
    }

    // To test low frequency level interrupt,
    // handler need to disable interrupt before it clear.
    // Interrupt is enabled by the host right before the test.
    // Disable and clear the interrupt at GPIO.
    CHECK_DIF_OK(dif_gpio_irq_set_enabled(&gpio, gpio_pin_irq_fired,
                                          kDifToggleDisabled));
    CHECK_DIF_OK(dif_gpio_irq_acknowledge(&gpio, gpio_pin_irq_fired));
    CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                                          plic_irq_id));
  }
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));

  rv_plic_testutils_irq_range_enable(
      &plic, kTopEarlgreyPlicTargetIbex0, kTopEarlgreyPlicIrqIdGpioGpio0,
      kTopEarlgreyPlicIrqIdGpioGpio0 + kDifGpioNumPins);

  // Anker for the host
  LOG_INFO("gpio_intr_test ");

  ujson_t uj = ujson_ottf_console();

  status_t s = command_processor(&uj);
  LOG_INFO("status = %r", s);
  return status_ok(s);
}
