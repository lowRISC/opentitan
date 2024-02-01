// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_
#include <stdint.h>

#include "sw/device/lib/dif/dif_rv_plic.h"

/**
 * OTTF global PLIC interface.
 */
extern dif_rv_plic_t ottf_plic;

/**
 * OTTF fault printing function.
 *
 * Called by exception handlers to print a fault code for unhandled
 * exceptions or interrupts. The printed message will be in the standard OTTF
 * form that can be detected by test automation.
 *
 * @param reason A string describing the fault reason.
 * @param mcause The value of the mcause register for this fault.
 */
void ottf_generic_fault_print(uint32_t *exc_info, const char *reason,
                              uint32_t mcause);

/**
 * OTTF exception handler.
 *
 * Called by the asm exception handler `handler_exception` subroutine.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_exception_handler(uint32_t *exc_info);

/**
 * OTTF instruction misaligned fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_instr_misaligned_fault_handler(uint32_t *exc_info);

/**
 * OTTF instruction access fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_instr_access_fault_handler(uint32_t *exc_info);

/**
 * OTTF illegal instruction fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_illegal_instr_fault_handler(uint32_t *exc_info);

/**
 * OTTF breakpoint handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_breakpoint_handler(uint32_t *exc_info);

/**
 * OTTF load/store fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_load_store_fault_handler(uint32_t *exc_info);

/**
 * OTTF machine-mode environment call handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_machine_ecall_handler(uint32_t *exc_info);

/**
 * OTTF user-mode environment call handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overridden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_user_ecall_handler(uint32_t *exc_info);

/**
 * OTTF software IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_software_isr(uint32_t *exc_info);

/**
 * OTTF timer IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_timer_isr(uint32_t *exc_info);

/**
 * OTTF external IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_external_isr(uint32_t *exc_info);

/**
 * OTTF external NMI internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_external_nmi_handler(uint32_t *exc_info);

/**
 * OTTF load integrity internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_load_integrity_error_handler(uint32_t *exc_info);

/**
 * OTTF internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overridden at link-time by providing an additional non-weak definition.
 */
void ottf_internal_isr(uint32_t *exc_info);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_
