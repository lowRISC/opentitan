// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"

// |extern| declarations to give the inline functions in the
// corresponding header a link location.
extern reg32_t reg32_from_addr(uintptr_t);
extern uint32_t reg32_read(reg32_t, ptrdiff_t);
extern void reg32_write(reg32_t, ptrdiff_t, uint32_t);
extern uint32_t reg32_read_mask(reg32_t, ptrdiff_t, uint32_t, uint32_t);
extern bool reg32_get_bit(reg32_t, ptrdiff_t, uint32_t);
extern void reg32_nonatomic_clear_mask(reg32_t, ptrdiff_t, uint32_t, uint32_t);
extern void reg32_nonatomic_set_mask(reg32_t, ptrdiff_t, uint32_t, uint32_t);
extern void reg32_nonatomic_clear_bit(reg32_t, ptrdiff_t, uint32_t);
extern void reg32_nonatomic_set_bit(reg32_t, ptrdiff_t, uint32_t);
