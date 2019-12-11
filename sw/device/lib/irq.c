// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/irq.h"

#include "sw/device/lib/base/stdasm.h"

static const uint32_t IRQ_EXT_ENABLE_OFFSET = 11;
static const uint32_t IRQ_TIMER_ENABLE_OFFSET = 7;
static const uint32_t IRQ_SW_ENABLE_OFFSET = 3;

void irq_set_vector_offset(uintptr_t address) {
  asm volatile("csrw mtvec, %0" ::"r"(address));
}

static void irq_mie_set(uint32_t value) {
  asm volatile("csrrs zero, mie, %0" : : "r"(value) :);
}

static void irq_mie_clr(uint32_t value) {
  asm volatile("csrrc zero, mie, %0" : : "r"(value) :);
}

void irq_global_ctrl(bool en) {
  if (en) {
    asm volatile("csrsi mstatus, 0x8" : : :);
  } else {
    asm volatile("csrci mstatus, 0x8" : : :);
  }
}

void irq_external_ctrl(bool en) {
  const uint32_t value = 1 << IRQ_EXT_ENABLE_OFFSET;
  if (en) {
    irq_mie_set(value);
  } else {
    irq_mie_clr(value);
  }
}

void irq_timer_ctrl(bool en) {
  const uint32_t value = 1 << IRQ_TIMER_ENABLE_OFFSET;
  if (en) {
    irq_mie_set(value);
  } else {
    irq_mie_clr(value);
  }
}

void irq_software_ctrl(bool en) {
  const uint32_t value = 1 << IRQ_SW_ENABLE_OFFSET;
  if (en) {
    irq_mie_set(value);
  } else {
    irq_mie_clr(value);
  }
}
