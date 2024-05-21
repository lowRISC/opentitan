// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%doc>
    This file is the "auto-generated DIF library header template", which
    provides some mandatory DIFs prototypes, that are similar across all IPs.
    This template is rendered into a .inc file that is included by the semi-
    auto-generated DIF header file (see util/make_new_dif/dif_template.h.tpl).
    Note, since this template is designed to manifest as a non-standalone header
    it has the file extension, .inc.

    For more information, see: https://github.com/lowRISC/opentitan/issues/8142

    Note, this template requires the following Python objects to be passed:

    1. ip: See util/make_new_dif.py for the definition of the `ip` obj.
</%doc>

#ifndef OPENTITAN_SW_IP_${ip.name_upper}_DIF_DIF_${ip.name_upper}_H_
#define OPENTITAN_SW_IP_${ip.name_upper}_DIF_DIF_${ip.name_upper}_H_

${autogen_banner}

/**
 * @file
 * @brief <a href="/hw/ip/${ip.name_snake}/doc/">${ip.name_upper}</a> Device Interface Functions
 *
 * The PLIC should be largely compatible with the (currently draft) [RISC-V PLIC
 * specification][plic], but tailored for the OpenTitan rv_plic register
 * addresses. We intend to make the addresses compatible with the PLIC
 * specification in the near future.
 *
 * [plic]: https://github.com/riscv/riscv-plic-spec/blob/master/riscv-plic.adoc
 */

#include "sw/ip/base/dif/dif_base.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/mmio.h"

#include "sw/ip/${ip.name_snake}/dif/autogen/dif_${ip.name_snake}_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The lowest interrupt priority.
 */
extern const uint32_t kDif${ip.name_camel}MinPriority;

/**
 * The highest interrupt priority.
 */
extern const uint32_t kDif${ip.name_camel}MaxPriority;

/**
 * A ${ip.name_long_upper} interrupt source identifier.
 *
 * This corresponds to a specific interrupt, and not the device it originates
 * from.
 *
 * This is an unsigned 32-bit value that is at least zero and is less than the
 * `NumSrc` instantiation parameter of the `${ip.name_snake}` device.
 *
 * The value 0 corresponds to "No Interrupt".
 */
typedef uint32_t dif_${ip.name_snake}_irq_id_t;

/**
 * A ${ip.name_long_upper} interrupt target.
 *
 * This corresponds to a specific system that can service an interrupt. In
 * OpenTitan's case, that is the Ibex core. If there were multiple cores in the
 * system, each core would have its own specific interrupt target ID.
 *
 * This is an unsigned 32-bit value that is at least 0 and is less than the
 * `NumTarget` instantiation parameter of the `${ip.name_snake}` device.
 */
typedef uint32_t dif_${ip.name_snake}_target_t;

/**
 * Resets the ${ip.name_long_upper} to a clean state.
 *
 * This function resets all the relevant ${ip.name_long_upper} registers,
 * apart from the CC register. There is no reliable way of knowing the ID
 * of an IRQ that has claimed the CC register, so we assume that the previous
 * "owner" of the resource has cleared/completed the CC access.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_reset(const dif_${ip.name_snake}_t *plic);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_is_pending(const dif_${ip.name_snake}_t *plic,
                                             dif_${ip.name_snake}_irq_id_t irq,
                                             bool *is_pending);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param irq An interrupt type.
 * @param target An interrupt target.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_get_enabled(const dif_${ip.name_snake}_t *plic,
                                              dif_${ip.name_snake}_irq_id_t irq,
                                              dif_${ip.name_snake}_target_t target,
                                              dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * This operation does not affect IRQ generation in `target`, which
 * must be configured in the corresponding peripheral itself.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param irq An interrupt type.
 * @param target An interrupt target.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_set_enabled(const dif_${ip.name_snake}_t *plic,
                                              dif_${ip.name_snake}_irq_id_t irq,
                                              dif_${ip.name_snake}_target_t target,
                                              dif_toggle_t state);

/**
 * Sets IRQ source priority (0-3).
 *
 * In order for the PLIC to set a Claim/Complete register and assert the
 * external interrupt line to the target (Ibex, ...), the priority of the IRQ
 * source must be higher than the threshold for this source.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param irq An interrupt type.
 * @param priority Priority to set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_set_priority(const dif_${ip.name_snake}_t *plic,
                                               dif_${ip.name_snake}_irq_id_t irq,
                                               uint32_t priority);

/**
 * Sets the target priority threshold.
 *
 * Sets the target priority threshold. PLIC will only interrupt a target when
 * IRQ source priority is set higher than the priority threshold for the
 * corresponding target.
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param target Target to set the IRQ priority threshold for.
 * @param threshold IRQ priority threshold to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_target_set_threshold(
    const dif_${ip.name_snake}_t *plic, dif_${ip.name_snake}_target_t target,
    uint32_t threshold);

/**
 * Claims an IRQ and gets the information about the source.
 *
 * Claims an IRQ and returns the IRQ related data to the caller. This function
 * reads a target specific Claim/Complete register. #dif_${ip.name_snake}_irq_complete
 * must be called in order to allow another interrupt with the same source id to
 * be delivered. This usually would be done once the interrupt has been
 * serviced.
 *
 * Another IRQ can be claimed before a prior IRQ is completed. In this way, this
 * functionality is compatible with nested interrupt handling. The restriction
 * is that you must Complete a Claimed IRQ before you will be able to claim an
 * IRQ with the same ID. This allows a pair of Claim/Complete calls to be
 * overlapped with another pair -- and there is no requirement that the
 * interrupts should be Completed in the reverse order of when they were
 * Claimed.
 *
 * @see #dif_${ip.name_snake}_irq_complete
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param target Target that claimed the IRQ.
 * @param[out] claim_data Data that describes the origin of the IRQ.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_claim(const dif_${ip.name_snake}_t *plic,
                                        dif_${ip.name_snake}_target_t target,
                                        dif_${ip.name_snake}_irq_id_t *claim_data);

/**
 * Completes the claimed IRQ.
 *
 * Finishes servicing of the claimed IRQ by writing the IRQ source ID back to a
 * target specific Claim/Complete register. This function must be called after
 * #dif_{ip.name_snake}_irq_claim, when the caller is prepared to service another IRQ
 * with the same source ID. If a source ID is never Completed, then when future
 * interrupts are Claimed, they will never have the source ID of the uncompleted
 * IRQ.
 *
 * @see #dif_{ip.name_snake}_irq_claim
 *
 * @param plic A ${ip.name_long_upper} handle.
 * @param target Target that claimed the IRQ.
 * @param complete_data Previously claimed IRQ data that is used to signal
 *        PLIC of the IRQ servicing completion.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_complete(
    const dif_${ip.name_snake}_t *plic, dif_${ip.name_snake}_target_t target,
    dif_${ip.name_snake}_irq_id_t complete_data);

/**
 * Forces the software interrupt for a particular target.
 *
 * This function causes an interrupt to the `target` HART to be serviced as if
 * hardware had asserted it.
 *
 * This function allows to synchronise between the HARTs, which otherwise
 * would not be possible due to HART being only able to access own CSRs.
 * NOTE: this is not an issue on Ibex, as it has only one HART.
 *
 * An interrupt handler is expected to call
 * `dif_rv_plic_software_irq_acknowledge` when the interrupt has been handled.
 *
 * @param plic ${ip.name_long_upper} state data.
 * @param target Target HART.
 * @return `dif_result_t`.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_software_irq_force(
    const dif_${ip.name_snake}_t *plic, dif_${ip.name_snake}_target_t target);

/**
 * Acknowledges the software interrupt for a particular target.
 *
 * This function indicates to the hardware that the software interrupt has been
 * successfully serviced. It is expected to be called from a software interrupt
 * handler.
 *
 * @param plic ${ip.name_long_upper} state data.
 * @param target Target HART.
 * @return `dif_result_t`.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_software_irq_acknowledge(
    const dif_${ip.name_snake}_t *plic, dif_${ip.name_snake}_target_t target);

/**
 * Returns software interrupt pending state for a particular target.
 *
 * @param plic ${ip.name_long_upper} state data.
 * @param target Target HART.
 * @param[out] is_pending Flag indicating whether the interrupt is pending.
 * @return `dif_result_t`.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_software_irq_is_pending(
    const dif_${ip.name_snake}_t *plic, dif_${ip.name_snake}_target_t target,
    bool *is_pending);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_IP_${ip.name_upper}_DIF_DIF_${ip.name_upper}_H_
