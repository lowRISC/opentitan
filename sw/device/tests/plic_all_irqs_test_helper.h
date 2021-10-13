// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PLIC_ALL_IRQS_TEST_HELPER_H_
#define OPENTITAN_SW_DEVICE_TESTS_PLIC_ALL_IRQS_TEST_HELPER_H_

/**
 * Helper macros used by the auto-generated test ./autogen/plic_all_irqs_test.c
 *
 * These are not meant to be used in any other tests.
 */

/**
 * Handles an IRQ from a peripheral instance.
 */
#define PERIPHERAL_ISR(peripheral, handle, plic_start_irq)                    \
  do {                                                                        \
    /* Correlate the interrupt fired at PLIC with the peripheral. */          \
    dif_##peripheral##_irq_t irq = (dif_##peripheral##_irq_t)(                \
        plic_irq_id - (dif_rv_plic_irq_id_t)plic_start_irq);                  \
    CHECK(irq == peripheral##_irq_expected,                                   \
          "Incorrect " #handle " IRQ received at PLIC: exp = %d, obs = %d",   \
          peripheral##_irq_expected, irq);                                    \
    peripheral##_irq_serviced = irq;                                          \
                                                                              \
    /* Check if the same interrupt fired at the peripheral as well. */        \
    /* TODO: read the whole status register to confirm none other pending. */ \
    bool is_pending;                                                          \
    CHECK_DIF_OK(                                                             \
        dif_##peripheral##_irq_is_pending(&handle, irq, &is_pending));        \
    CHECK(is_pending, "Interrupt %d fired at PLIC did not fire at " #handle,  \
          irq);                                                               \
                                                                              \
    /* Clear the interrupt at the peripheral. */                              \
    CHECK_DIF_OK(dif_##peripheral##_irq_acknowledge(&handle, irq));           \
  } while (0)

/**
 * Initializes the handle to a peripheral instance.
 */
#define PERIPHERAL_INIT(peripheral, handle, base_addr)     \
  do {                                                     \
    mmio_region_t addr = mmio_region_from_addr(base_addr); \
    CHECK_DIF_OK(dif_##peripheral##_init(addr, &handle));  \
  } while (0)

/**
 * Clears all previous interrupt invocations.
 */
#define PERIPHERAL_IRQS_CLEAR(handle)                                         \
  do {                                                                        \
    /* TODO(#8142): Replace with dif_<ip>_irq_acknowledge_all when available. \
     */                                                                       \
    mmio_region_write32(handle.base_addr, 0, (uint32_t)ULONG_MAX);            \
  } while (0)

/**
 * Enables all IRQs in the given peripheral instance.
 */
#define PERIPHERAL_IRQS_ENABLE(peripheral, handle)                        \
  do {                                                                    \
    dif_##peripheral##_irq_state_snapshot_t all_irqs =                    \
        (dif_##peripheral##_irq_state_snapshot_t)ULONG_MAX;               \
    CHECK_DIF_OK(dif_##peripheral##_irq_restore_all(&handle, &all_irqs)); \
  } while (0)

/**
 * Triggers all IRQs in a peripherals instance one-by-one.
/*/
#define PERIPHERAL_IRQS_TRIGGER(peripheral, handle, plic_peripheral,           \
                                start_irq, end_irq)                            \
  do {                                                                         \
    peripheral_expected = plic_peripheral;                                     \
    for (dif_##peripheral##_irq_t irq = start_irq; irq <= end_irq; ++irq) {    \
      peripheral##_irq_expected = irq;                                         \
      LOG_INFO("Triggering " #handle " IRQ %d.", irq);                         \
      CHECK_DIF_OK(dif_##peripheral##_irq_force(&handle, irq));                \
      /* NOTE: The interrupt triggered above is instantaneous - Ibex jumps     \
       * into the ISR even before a WFI can be called. Hence, we do nothing.   \
       */                                                                      \
      CHECK(peripheral##_irq_serviced == irq,                                  \
            "Incorrect " #peripheral " irq serviced: exp = %d, obs = %d", irq, \
            peripheral##_irq_serviced);                                        \
      LOG_INFO("IRQ %d from " #handle " is serviced.", irq);                   \
    }                                                                          \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_TESTS_PLIC_ALL_IRQS_TEST_HELPER_H_
