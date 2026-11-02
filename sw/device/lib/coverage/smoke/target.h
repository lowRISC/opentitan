// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_SMOKE_TARGET_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_SMOKE_TARGET_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

void covfunc_hit(void);

inline void inline_covfunc_hit(void) {}

static inline void static_inline_covfunc_hit(void) {}

void covfunc_miss(void);

inline void inline_covfunc_miss(void) {}

static inline void static_inline_covfunc_miss(void) {}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_SMOKE_TARGET_H_
