// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SW_DEVICE_LIB_RUNTIME_IRQ_H_
#define SW_DEVICE_LIB_RUNTIME_IRQ_H_

#include <stdbool.h>
#include <stdint.h>

// TODO: remove this dependency on common.h.
#include "sw/device/lib/common.h"

/**
 * Functions and types for controlling and handling interrupts.
 *
 * Note that, currently, some parts of this file are Ibex-specific.
 */

/**
 * An irq_type_t represents an interrupt request type.
 *
 * The value of each enumerator corresponds to the bit index of the interrupt
 * in the |mie| (machine interrupt enable) CSR.
 */
typedef enum irq_type {
  kIrqException = 0,
  kIrqSoftware = 3,
  kIrqTimer = 7,
  kIrqExternal = 11,
  kIrqNmi = 31
} irq_type_t;

/**
 * An irq_handler_t represents a callable virtual interrupt handler.
 *
 * Note that this is not a "real" interrupt handler, in that it has to conform
 * to the IRQ calling convention; it should have the standard RISC-V calling
 * convention.
 */
typedef void (*irq_handler_t)(void);

/**
 * The global interrupt handler vtable.
 *
 * When an interrupt is serviced for interrupt type |t|, control will reach the
 * function pointer at |irq_vtable[N]|.
 *
 * Mutating |irq_vtable[0]| is, for the time being, Undefined Behavior.
 */
extern irq_handler_t irq_vtable[32];

/**
 * An exception_type_t represents a hardware exception type.
 *
 * The value of the enumerator corresponds to the value that would appear in the
 * bottom five bits of the |mcause| register during a trap.
 */
typedef enum exception_type {
  kMisalignedProgramCounter = 0,
  kInstructionAccessFault = 1,
  kIllegalInstruction = 2,
  kBreakpoint = 3,
  kLoadAccessFault = 5,
  kStoreAccessFault = 7,
  kEcallUser = 8,
  kEcallMachine = 11,
} exception_type_t;

/**
 * Get a static string describing a particular exception type.
 *
 * @return a static string, for user-display only.
 */
const char *describe_exception(exception_type_t cause);

/**
 * An exception_handler_t represents a virtual exception handler.
 *
 * Like |irq_handler_t|, such functions should have the standard, rather than
 * the IRQ, calling convention.
 */
typedef void (*exception_handler_t)(exception_type_t cause);

/**
 * The global exception handler vtable.
 *
 * When a servicing a hardware register of type |t|, control will flow to the
 * function pointer at |exception_vtable[t]|.
 */
extern exception_handler_t exception_vtable[32];

/**
 * Returns the cause of the current exception being serviced.
 *
 * Calling this function outside of an exception handler is Undefined Behavior.
 *
 * @return a valid exception type.
 */
exception_type_t get_exception_cause(void);

/**
 * Returns the value of the |mtval| register, which contains trap-specific
 * information.
 *
 * For example, during an illegal instruction fault, this would be the offending
 * instruction word.
 *
 * Calling this function outside of an interrupt or exception handler is
 * Undefined Behavior.
 *
 * @return an otherwise unspecified trap-specific value.
 */
uint32_t get_trap_value(void);

/**
 * Sets the location of the global interrupt vector. In general, this function
 * should not be called except during runtime setup.
 *
 * @arg irq_vector a 256-bit aligned pointer to the new global interrupt vector.
 */
void set_irq_vector(void *irq_vector);

/**
 * Sets whether all interrupts are enabled.
 *
 * @arg enable whether to enable all interrupts.
 */
void irq_global_set_enabled(bool enabled);

/**
 * Sets whether a particular interrupt is enabled.
 *
 * This function may have no effect, such as when attempting to disable NMI.
 *
 * @arg type which interrupt to enable.
 * @arg enable whether to enable this particular interrupt.
 */
void irq_set_enabled(irq_type_t type, bool enabled);

#endif  // SW_DEVICE_LIB_RUNTIME_IRQ_H_
