// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_IRQ_H_
#define OPENTITAN_SW_DEVICE_LIB_IRQ_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * Update to the location of vectors as specificed in the linker file
 *
 * The address must be 256-byte aligned.
 */
void irq_set_vector_offset(uintptr_t address);

/**
 * Enable / disable ibex globlal interrupts
 */
void irq_global_ctrl(bool en);

/**
 * Enable / disable ibex external interrupts
 */
void irq_external_ctrl(bool en);

/**
 * Enable / disable ibex timer interrupts
 */
void irq_timer_ctrl(bool en);

/**
 * Enable / disable ibex software interrupts
 */
void irq_software_ctrl(bool en);

#endif  // OPENTITAN_SW_DEVICE_LIB_IRQ_H_
