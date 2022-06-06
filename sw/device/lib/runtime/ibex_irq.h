// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_IRQ_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_IRQ_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * Update to the location of vectors as specificed in the linker file
 *
 * The address must be 256-byte aligned.
 */
void ibex_irq_set_vector_offset(uintptr_t address);

/**
 * Enable / disable ibex globlal interrupts
 */
void ibex_irq_global_ctrl(bool enable);

/**
 * Enable / disable ibex external interrupts
 */
void ibex_irq_external_ctrl(bool enable);

/**
 * Enable / disable ibex timer interrupts
 */
void ibex_irq_timer_ctrl(bool enable);

/**
 * Enable / disable ibex software interrupts
 */
void ibex_irq_software_ctrl(bool enable);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_IRQ_H_
