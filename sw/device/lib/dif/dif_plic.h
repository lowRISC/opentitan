// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/** The lowest interrupt priority. */
extern const uint32_t kDifPlicMinPriority;

/** The highest interrupt priority. */
extern const uint32_t kDifPlicMaxPriority;

/**
 * PLIC interrupt source identifier.
 *
 * This corresponds to a specific interrupt, and not the device it originates
 * from.
 *
 * This is an unsigned 32-bit value that is at least zero and is less than the
 * `NumSrc` instantiation parameter of the `rv_plic` device.
 *
 * The value 0 corresponds to "No Interrupt".
 */
typedef uint32_t dif_plic_irq_id_t;

/**
 * PLIC interrupt target.
 *
 * This corresponds to a specific system that can service an interrupt. In
 * OpenTitan's case, that is the Ibex core. If there were multiple cores in the
 * system, each core would have its own specific interrupt target ID.
 *
 * This is an unsigned 32-bit value that is at least 0 and is less than the
 * `NumTarget` instantiation parameter of the `rv_plic` device.
 */
typedef uint32_t dif_plic_target_t;

/**
 * Generic enable/disable enumeration.
 *
 * Enumeration used to enable/disable bits, flags, ...
 */
typedef enum dif_plic_enable {
  kDifPlicEnable = 0,
  kDifPlicDisable,
} dif_plic_enable_t;

/**
 * Generic set/unset enumeration.
 *
 * Enumeration used to set/unset, or get the state of bits,flags ...
 */
typedef enum dif_plic_flag {
  kDifPlicSet = 0,
  kDifPlicUnset,
} dif_plic_flag_t;

/**
 * PLIC instance state.
 *
 * PLIC persistent data that is required by all the PLIC API.
 */
typedef struct dif_plic {
  mmio_region_t base_addr; /**< PLIC instance base address. */
} dif_plic_t;

/**
 * PLIC generic status codes.
 *
 * These error codes can be used by any function. However if a function
 * requires additional status codes, it must define a set of status codes to
 * be used exclusicvely by such function.
 */
typedef enum dif_plic_result {
  kDifPlicOk = 0, /**< Success. */
  kDifPlicError,  /**< General error. */
  kDifPlicBadArg, /**< Input parameter is not valid. */
} dif_plic_result_t;

/**
 * Initialises an instance of PLIC.
 *
 * Information that must be retained, and is required to program PLIC, shall
 * be stored in `plic`.
 *
 * @param base_addr Base address of an instance of the PLIC IP block.
 * @param plic PLIC state data.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_init(mmio_region_t base_addr, dif_plic_t *plic);

/**
 * Enables/disables handling of IRQ source in PLIC.
 *
 * This operation does not affect the IRQ generation in the peripherals, which
 * must be configured in a corresponding peripheral itself.
 * @param plic PLIC state data.
 * @param irq Interrupt Source ID.
 * @param target Target to enable the IRQ for.
 * @param enable Enable/disable the IRQ handling.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_enable_set(const dif_plic_t *plic,
                                          dif_plic_irq_id_t irq,
                                          dif_plic_target_t target,
                                          dif_plic_enable_t enable);

/**
 * Sets the IRQ trigger type (edge/level).
 *
 * Sets the behaviour of the Interrupt Gateway for a particular IRQ to be edge
 * or level triggered.
 * @param plic PLIC state data.
 * @param irq Interrupt source ID.
 * @param enable Enable for the edge triggered, disable for level triggered
 * IRQs.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_trigger_type_set(const dif_plic_t *plic,
                                                dif_plic_irq_id_t irq,
                                                dif_plic_enable_t enable);

/**
 * Sets IRQ source priority (0-3).
 *
 * In order for PLIC to set a CC register and assert the external interrupt line
 * to the target (Ibex, ...), the priority of an IRQ source must be higher than
 * the threshold for this source.
 * @param plic PLIC state data.
 * @param irq Interrupt source ID.
 * @param priority Priority to be set.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_priority_set(const dif_plic_t *plic,
                                            dif_plic_irq_id_t irq,
                                            uint32_t priority);

/**
 * Sets the target priority threshold.
 *
 * Sets the target priority threshold. PLIC will only interrupt a target when
 * IRQ source priority is set higher than the priority threshold for the
 * corresponding target.
 * @param plic PLIC state data.
 * @param target Target to set the IRQ priority threshold for.
 * @param threshold IRQ priority threshold to be set.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_target_threshold_set(const dif_plic_t *plic,
                                                dif_plic_target_t target,
                                                uint32_t threshold);

/**
 * Checks the Interrupt Pending bit.
 *
 * Gets the status of the PLIC Interrupt Pending register bit for a specific IRQ
 * source.
 * @param plic PLIC state data.
 * @param irq Interrupt source ID.
 * @param status Flag indicating whether the IRQ pending bit is set in PLIC.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_pending_status_get(const dif_plic_t *plic,
                                                  dif_plic_irq_id_t irq,
                                                  dif_plic_flag_t *status);

/**
 * Claims an IRQ and gets the information about the source.
 *
 * Claims an IRQ and returns the IRQ related data to the caller. This function
 * reads a target specific CC register. dif_plic_irq_complete must be called
 * after the claimed IRQ has been serviced.
 *
 * @param plic PLIC state data.
 * @param target Target that claimed the IRQ.
 * @param claim_data Data that describes the origin of the IRQ.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_claim(const dif_plic_t *plic,
                                     dif_plic_target_t target,
                                     dif_plic_irq_id_t *claim_data);

/**
 * Completes the claimed IRQ.
 *
 * Finishes servicing of the claimed IRQ by writing the IRQ source ID back to a
 * target specific CC register. This function must be called after
 * dif_plic_claim_irq, when a caller has finished servicing the IRQ.
 *
 * @param plic PLIC state data.
 * @param target Target that claimed the IRQ.
 * @param complete_data Previously claimed IRQ data that is used to signal PLIC
 *                      of the IRQ servicing completion.
 * @return `dif_plic_result_t`.
 */
dif_plic_result_t dif_plic_irq_complete(const dif_plic_t *plic,
                                        dif_plic_target_t target,
                                        const dif_plic_irq_id_t *complete_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_
