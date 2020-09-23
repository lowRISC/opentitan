// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_gpio.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_plic.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
static dif_plic_t plic;

// These constants reflect the GPIOs exposed by the GPIO IP.
static const uint32_t kNumGpios = 32;
static const uint32_t kGpiosMask = 0xffffffff;

// These constants reflect the GPIOs exposed by the OpenTitan SoC.
static const uint32_t kNumChipGpios = 16;
// TODO #2484: GPIO pins 16-19 are special inputs - do not touch them.
static const uint32_t kGpiosAllowedMask = 0xfff0ffff;
static const uint32_t kChipGpiosMask = 0xffff & kGpiosAllowedMask;

// These indicate the GPIO pin irq expected to fire, declared volatile since
// they are used by the interrupt handler.
static volatile uint32_t expected_gpio_pin_irq;
static volatile bool expected_irq_edge;

/**
 * GPIO test - verifies the GPIO pins in the input and output directions.
 *
 * In the output direction, SW writes the following pattern:
 * 1. Start with GPIOs = all zeros
 * 2. Walk a 1 through ALL GPIOs (presented by the IP), read `data_in` with each
 *    write to ensure correctness
 * 3. Set all GPIOs to 0s, followed by all 1s.
 * 4. Walk a 0 through ALL GPIOs (presented by the IP), read `data_in` with each
 *    write to ensure correctness
 * 5. Set all GPIOs to 1s, followed by all 0s.
 *
 * The correctness of the GPIO values on the chip pins is verified by the
 * external testbench. The correctness of `data_in` is limited to the number of
 * GPIOs exposed by the chip, so we mask the written value accordingly. In
 * addition, some GPIOs are used for 'special' functionality - JTAG TRST_N and
 * SRST_N. We do not touch those (via mask). This will change when the jtag_mux
 * functionality is moved into pinmux.
 *
 * In the input direction, the external testbench sends the following pattern:
 * 1. Walk a 1 in 'temperature' pattern (0001, 0011, 0111, 1111, 1110, 100, ..)
 *
 * Both, rising and falling edges are configured for generating an interrupt. As
 * each pin rises or falls, the SW checks the interrupt, status and `data_in`
 * for correctness.
 */

/**
 * Initializes PLIC and enables all GPIO interrupts.
 */
static void plic_init_with_irqs(mmio_region_t base_addr, dif_plic_t *plic) {
  LOG_INFO("Initializing the PLIC.");

  CHECK(dif_plic_init((dif_plic_params_t){.base_addr = base_addr}, plic) ==
            kDifPlicOk,
        "dif_plic_init failed");

  for (uint32_t i = 0; i < kNumGpios; ++i) {
    dif_plic_irq_id_t plic_irq_id = i + kTopEarlgreyPlicIrqIdGpioGpio0;

    // Enable GPIO interrupts at PLIC as edge triggered.
    CHECK(dif_plic_irq_set_trigger(plic, plic_irq_id, kDifPlicIrqTriggerEdge) ==
              kDifPlicOk,
          "dif_plic_irq_set_trigger failed");

    // Set the priority of GPIO interrupts at PLIC to be >=1
    CHECK(dif_plic_irq_set_priority(plic, plic_irq_id, 0x1) == kDifPlicOk,
          "dif_plic_irq_set_priority failed");

    // Enable all GPIO interrupts at the PLIC.
    CHECK(
        dif_plic_irq_set_enabled(plic, plic_irq_id, kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");
  }

  // Set the threshold for the Ibex to 0.
  CHECK(dif_plic_target_set_threshold(plic, kTopEarlgreyPlicTargetIbex0, 0x0) ==
            kDifPlicOk,
        "dif_plic_target_set_threshold failed");
}

/**
 * Runs the GPIO output test.
 *
 * Walks a 1 over the GPIO pins, followed by walking a 0.
 * The external testbench checks the GPIO values for correctness.
 */
static void gpio_output_test(const dif_gpio_t *gpio) {
  LOG_INFO("Starting GPIO output test");

  // Set the GPIOs to be in output mode.
  CHECK(dif_gpio_output_set_enabled_all(gpio, kGpiosAllowedMask) == kDifGpioOk,
        "dif_gpio_output_set_enabled_all failed");

  // Walk 1s - 0001, 0010, 0100, 1000, etc.
  for (uint32_t i = 0; i < kNumGpios; ++i) {
    uint32_t gpio_val = 1 << i;
    CHECK(dif_gpio_write_all(gpio, gpio_val) == kDifGpioOk,
          "dif_gpio_write_all failed");

    // Read GPIO_IN to confirm what we wrote.
    uint32_t read_val;
    CHECK(dif_gpio_read_all(gpio, &read_val) == kDifGpioOk,
          "dif_gpio_read_all failed");

    // Check written and read val for correctness.
    // Though we try to set all available GPIOs, only the ones that are exposed
    // as chip IOs can be read back. So we mask the values with
    // `kChipGpiosMask`.
    gpio_val &= kChipGpiosMask;
    read_val &= kChipGpiosMask;
    CHECK(gpio_val == read_val, "GPIOs mismatched (written = %x, read = %x)",
          gpio_val, read_val);
  }

  // Write all 0s to the GPIOs.
  CHECK(dif_gpio_write_all(gpio, ~kGpiosMask) == kDifGpioOk,
        "dif_gpio_write_all failed");

  // Write all 1s to the GPIOs.
  CHECK(dif_gpio_write_all(gpio, kGpiosMask) == kDifGpioOk,
        "dif_gpio_write_all failed");

  // Now walk 0s - 1110, 1101, 1011, 0111, etc.
  for (uint32_t i = 0; i < kNumGpios; ++i) {
    uint32_t gpio_val = ~(1 << i);
    CHECK(dif_gpio_write_all(gpio, gpio_val) == kDifGpioOk,
          "dif_gpio_write_all failed");

    // Read GPIO_IN to confirm what we wrote.
    uint32_t read_val;
    CHECK(dif_gpio_read_all(gpio, &read_val) == kDifGpioOk,
          "dif_gpio_read_all failed");

    // Check written and read val for correctness.
    // Though we try to set all available GPIOs, only the ones that are exposed
    // as chip IOs can be read back. So we mask the values with
    // `kChipGpiosMask`.
    gpio_val &= kChipGpiosMask;
    read_val &= kChipGpiosMask;
    CHECK(gpio_val == read_val, "GPIOs mismatched (written = %x, read = %x)",
          gpio_val, read_val);
  }

  // Write all 1s to the GPIOs.
  CHECK(dif_gpio_write_all(gpio, kGpiosMask) == kDifGpioOk,
        "dif_gpio_write_all failed");

  // Write all 0s to the GPIOs.
  CHECK(dif_gpio_write_all(gpio, ~kGpiosMask) == kDifGpioOk,
        "dif_gpio_write_all failed");
}

/**
 * Runs the GPIO input test.
 *
 * We start off with all 0s. The function polls the GPIOs for a 'thermometer
 * code' pattern (0, 1, 11, 111 etc) which is driven by the testbench, through
 * interrupts. The rising edge of each subsequent pin causes an interrupt to
 * fire. The ISR checks for the right GPIO and polarity. The testbench then
 * reverses the thermometer pattern (1111, 1110, 1100, 1000, etc).to capture the
 * interrupt on the falling edge.
 */
static void gpio_input_test(const dif_gpio_t *gpio) {
  LOG_INFO("Starting GPIO input test");

  // Enable the noise filter on all GPIOs.
  CHECK(dif_gpio_input_noise_filter_set_enabled(
            gpio, kGpiosAllowedMask, kDifGpioToggleEnabled) == kDifGpioOk,
        "dif_gpio_input_noise_filter_set_enabled failed");

  // Configure all GPIOs to be rising and falling edge interrupts.
  CHECK(dif_gpio_irq_set_trigger(gpio, kGpiosAllowedMask,
                                 kDifGpioIrqTriggerEdgeRisingFalling) ==
            kDifGpioOk,
        "dif_gpio_irq_set_trigger failed");

  // Enable interrupts on all GPIOs.
  CHECK(dif_gpio_irq_set_enabled_masked(gpio, kGpiosAllowedMask,
                                        kDifGpioToggleEnabled) == kDifGpioOk,
        "dif_gpio_irq_set_enabled_masked failed");

  // Set the GPIOs to be in input mode.
  CHECK(dif_gpio_output_set_enabled_all(gpio, 0u) == kDifGpioOk,
        "dif_gpio_output_set_enabled_all failed");

  // Wait for rising edge interrupt on each pin.
  expected_irq_edge = true;
  for (expected_gpio_pin_irq = 0; expected_gpio_pin_irq < kNumChipGpios;
       ++expected_gpio_pin_irq) {
    wait_for_interrupt();
  }

  // Wait for falling edge interrupt on each pin.
  expected_irq_edge = false;
  for (expected_gpio_pin_irq = 0; expected_gpio_pin_irq < kNumChipGpios;
       ++expected_gpio_pin_irq) {
    wait_for_interrupt();
  }
}

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default external irq handler in
 * `sw/device/lib/handler.h`.
 */
void handler_irq_external(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_plic_irq_id_t plic_irq_id;
  CHECK(dif_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &plic_irq_id) ==
            kDifPlicOk,
        "dif_plic_irq_claim failed");

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == kTopEarlgreyPlicPeripheralGpio,
        "Interrupt from incorrect peripheral: (exp: %d, obs: %s)",
        kTopEarlgreyPlicPeripheralGpio, peripheral);

  // Correlate the interrupt fired from GPIO.
  uint32_t gpio_pin_irq_fired = plic_irq_id - kTopEarlgreyPlicIrqIdGpioGpio0;

  // Check if we did expect the right GPIO IRQ to fire.
  CHECK(gpio_pin_irq_fired == expected_gpio_pin_irq,
        "Incorrect GPIO interrupt (exp: %d, obs: %d)", expected_gpio_pin_irq,
        gpio_pin_irq_fired);

  // Check if the same interrupt fired at GPIO as well.
  uint32_t gpio_irqs_status;
  CHECK(dif_gpio_irq_is_pending_all(&gpio, &gpio_irqs_status) == kDifGpioOk,
        "dif_gpio_irq_is_pending_all failed");
  CHECK(gpio_irqs_status == (1 << expected_gpio_pin_irq),
        "Incorrect GPIO irqs status {exp: %x, obs: %x}",
        (1 << expected_gpio_pin_irq), gpio_irqs_status);

  // Read the gpio pin value to ensure the right value is being reflected.
  bool pin_val;
  CHECK(dif_gpio_read(&gpio, expected_gpio_pin_irq, &pin_val) == kDifGpioOk,
        "dif_gpio_read failed");

  // Check if the pin value is set correctly.
  CHECK(pin_val == expected_irq_edge, "Incorrect GPIO %d pin value (exp: %b)",
        expected_gpio_pin_irq, expected_irq_edge);

  // Clear the interrupt at GPIO.
  CHECK(dif_gpio_irq_acknowledge(&gpio, gpio_pin_irq_fired) == kDifGpioOk,
        "dif_gpio_irq_acknowledge failed");

  // Complete the IRQ at PLIC.
  CHECK(dif_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                              &plic_irq_id) == kDifPlicOk,
        "dif_plic_irq_complete failed");
}

const test_config_t kTestConfig;

bool test_main(void) {
  // Initialize the pinmux - this assigns MIO0-31 to GPIOs.
  pinmux_init();

  // Initialize the GPIO.
  dif_gpio_params_t gpio_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  CHECK(dif_gpio_init(gpio_params, &gpio) == kDifGpioOk,
        "dif_gpio_init failed");

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  plic_init_with_irqs(plic_base_addr, &plic);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Run the tests.
  gpio_output_test(&gpio);
  gpio_input_test(&gpio);

  return true;
}
