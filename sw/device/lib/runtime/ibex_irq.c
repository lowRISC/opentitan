// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/ibex_irq.h"

#include "sw/device/lib/base/csr.h"

static const uint32_t kIrqExtEnableOffset = 11;
static const uint32_t kIrqTimerEnableOffset = 7;
static const uint32_t kIrqSwEnableOffset = 3;

void ibex_irq_set_vector_offset(uintptr_t address) {
  CSR_WRITE(CSR_REG_MTVEC, (uint32_t)address);
}

void ibex_irq_global_ctrl(bool enable) {
  if (enable) {
    CSR_SET_BITS(CSR_REG_MSTATUS, 0x8);
  } else {
    CSR_CLEAR_BITS(CSR_REG_MSTATUS, 0x8);
  }
}

void ibex_irq_external_ctrl(bool enable) {
  if (enable) {
    CSR_SET_BITS(CSR_REG_MIE, 1 << kIrqExtEnableOffset);
  } else {
    CSR_CLEAR_BITS(CSR_REG_MIE, 1 << kIrqExtEnableOffset);
  }
}

void ibex_irq_timer_ctrl(bool enable) {
  if (enable) {
    CSR_SET_BITS(CSR_REG_MIE, 1 << kIrqTimerEnableOffset);
  } else {
    CSR_CLEAR_BITS(CSR_REG_MIE, 1 << kIrqTimerEnableOffset);
  }
}

void ibex_irq_software_ctrl(bool enable) {
  if (enable) {
    CSR_SET_BITS(CSR_REG_MIE, 1 << kIrqSwEnableOffset);
  } else {
    CSR_CLEAR_BITS(CSR_REG_MIE, 1 << kIrqSwEnableOffset);
  }
}
