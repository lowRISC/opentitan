// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RV_TIMER_H_
#define OPENTITAN_SW_DEVICE_LIB_RV_TIMER_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * Set hart timer prescaler
 *
 * Program hart timer prescaler to produce 1us ticks
 *
 * @param hart hart selection
 */
void rv_timer_set_us_tick(uint32_t hart);

/**
 * Set hart timer compare value
 *
 * Program hart timer compare value.  When this value is met, an interrupt will
 * be triggered.
 *
 * @param hart hart selection
 */
void rv_timer_set_cmp(uint32_t hart, uint64_t cmp);

/**
 * Enable hart timer to begin counting
 *
 * @param hart hart selection
 * @param en 1 enables timer, 0 disables timer
 */
void rv_timer_ctrl(uint32_t hart, bool en);

/**
 * Set hart timer interrupt enable
 *
 * @param hart hart selection
 * @param en 1 enables interrupt, 0 disables interrupt
 */
void rv_timer_intr_enable(uint32_t hart, bool en);

/**
 * Clear all active interrupts
 * Interrupt state clearing is W1C (write-one-clear)
 */
void rv_timer_clr_all_intrs(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_RV_TIMER_H_
