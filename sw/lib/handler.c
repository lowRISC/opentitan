// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "common.h"

/**
 * Default exception handler. Can be overidden.
 */
void handler_exception(void) __attribute__((aligned(4), interrupt, weak));

/**
 * SW IRQ handler. Can be overidden.
 */
void handler_irq_software(void) __attribute__((aligned(4), interrupt, weak));

/**
 * Timer IRQ handler. Can be overidden.
 */
void handler_irq_timer(void) __attribute__((aligned(4), interrupt, weak));

/**
 * external IRQ handler. Can be overidden.
 */
void handler_irq_external(void) __attribute__((aligned(4), interrupt, weak));

// Below functions are default weak exception handlers meant to be overriden
void handler_exception(void) {
  while (1) {
  }
}

void handler_irq_software(void) {
  while (1) {
  }
}

void handler_irq_timer(void) {
  while (1) {
  }
}

void handler_irq_external(void) {
  while (1) {
  }
}
