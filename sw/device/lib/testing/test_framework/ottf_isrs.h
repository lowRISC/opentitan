// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_

/**
 * OTTF exception handler.
 *
 * Called by the asm exception handler `handler_exception` subroutine.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_exception_handler(void);

/**
 * OTTF instruction misaligned fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_instr_misaligned_fault_handler(void);

/**
 * OTTF instruction access fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_instr_access_fault_handler(void);

/**
 * OTTF illegal instruction fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_illegal_instr_fault_handler(void);

/**
 * OTTF breakpoint handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_breakpoint_handler(void);

/**
 * OTTF load/store fault handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_load_store_fault_handler(void);

/**
 * OTTF machine-mode evironment call handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_machine_ecall_handler(void);

/**
 * OTTF user-mode evironment call handler.
 *
 * Called by default implementation of `ottf_exception_handler`. If that
 * function is overriden, this function may not be called.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_user_ecall_handler(void);

/**
 * OTTF software IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_software_isr(void);

/**
 * OTTF timer IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_timer_isr(void);

/**
 * OTTF external IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_external_isr(void);

/**
 * OTTF external NMI internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_external_nmi_handler(void);

/**
 * OTTF load integrity internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_load_integrity_error_handler(void);

/**
 * OTTF internal IRQ handler.
 *
 * `ottf_isrs.c` provides a weak definition of this symbol, which can be
 * overriden at link-time by providing an additional non-weak definition.
 */
void ottf_internal_isr(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ISRS_H_
