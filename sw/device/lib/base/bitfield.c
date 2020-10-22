// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/bitfield.h"

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern uint32_t bitfield_field32_read(uint32_t bitfield,
                                      bitfield_field32_t field);
extern uint32_t bitfield_field32_write(uint32_t bitfield,
                                       bitfield_field32_t field,
                                       uint32_t value);

extern bitfield_field32_t bitfield_bit32_to_field32(
    bitfield_bit32_index_t bit_index);

extern bool bitfield_bit32_read(uint32_t bitfield,
                                bitfield_bit32_index_t bit_index);
extern uint32_t bitfield_bit32_write(uint32_t bitfield,
                                     bitfield_bit32_index_t bit_index,
                                     bool value);

extern int32_t bitfield_find_first_set32(int32_t bitfield);
extern int32_t bitfield_count_leading_zeroes32(uint32_t bitfield);
extern int32_t bitfield_count_trailing_zeroes32(uint32_t bitfield);
extern int32_t bitfield_popcount32(uint32_t bitfield);
extern int32_t bitfield_parity32(uint32_t bitfield);
extern uint32_t bitfield_byteswap32(uint32_t bitfield);
