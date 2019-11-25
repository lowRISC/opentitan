// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _IRQ_H_
#define _IRQ_H_

#include "sw/device/lib/base/types.h"

/**
 * Update to the location of vectors as specificed in the linker file
 */
extern void update_mtvec(char *ptr);

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

#endif
