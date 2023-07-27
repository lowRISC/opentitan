// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"

// `extern` declarations to give the inline functions in the corresponding
// header a link location.

extern uint32_t launder32(uint32_t);
extern uintptr_t launderw(uintptr_t);
extern void barrier32(uint32_t);
extern void barrierw(uintptr_t);

extern ct_bool32_t ct_sltz32(int32_t);
extern ct_bool32_t ct_sltu32(uint32_t, uint32_t);
extern ct_bool32_t ct_sgeu32(uint32_t, uint32_t);
extern ct_bool32_t ct_seqz32(uint32_t);
extern ct_bool32_t ct_seq32(uint32_t, uint32_t);
extern uint32_t ct_cmov32(ct_bool32_t, uint32_t, uint32_t);

extern ct_boolw_t ct_sltzw(intptr_t);
extern ct_boolw_t ct_sltuw(uintptr_t, uintptr_t);
extern ct_boolw_t ct_sgeuw(uintptr_t, uintptr_t);
extern ct_boolw_t ct_seqzw(uintptr_t);
extern ct_boolw_t ct_seqw(uintptr_t, uintptr_t);
extern uintptr_t ct_cmovw(ct_boolw_t, uintptr_t, uintptr_t);
