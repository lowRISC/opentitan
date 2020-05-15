// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/bitfield.h"

// `extern` declarations to give the inline functions in the
// corresponding header a link location.
extern uint32_t bitfield_set_field32(uint32_t bitfield,
                                     bitfield_field32_t field);

extern uint32_t bitfield_get_field32(uint32_t bitfield,
                                     bitfield_field32_t field);
