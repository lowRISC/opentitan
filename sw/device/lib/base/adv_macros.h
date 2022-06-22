// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_ADV_MACROS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_ADV_MACROS_H_

#include "sw/device/lib/base/macros.h"

// The preprocessor techniques below are explained at
// https://github.com/pfultz2/Cloak/wiki/C-Preprocessor-tricks,-tips,-and-idioms

#define OT_IIF(c) OT_PRIMITIVE_CAT(OT_IIF_, c)
#define OT_IIF_0(t, ...) __VA_ARGS__
#define OT_IIF_1(t, ...) t

#define OT_CHECK_N(x, n, ...) n
#define OT_CHECK(...) OT_CHECK_N(__VA_ARGS__, 0, )
#define OT_PROBE(x) x, 1,

#define OT_NOT(x) OT_CHECK(OT_PRIMITIVE_CAT(OT_NOT_, x))
#define OT_NOT_0 OT_PROBE(~)

#define OT_EMPTY()
#define OT_DEFER(id) id OT_EMPTY()
#define OT_OBSTRUCT(...) __VA_ARGS__ OT_DEFER(OT_EMPTY)()
#define OT_EXPAND(...) __VA_ARGS__

#define OT_EVAL(...) OT_EVAL1(OT_EVAL1(OT_EVAL1(__VA_ARGS__)))
#define OT_EVAL1(...) OT_EVAL2(OT_EVAL2(OT_EVAL2(__VA_ARGS__)))
#define OT_EVAL2(...) OT_EVAL3(OT_EVAL3(OT_EVAL3(__VA_ARGS__)))
#define OT_EVAL3(...) OT_EVAL4(OT_EVAL4(OT_EVAL4(__VA_ARGS__)))
#define OT_EVAL4(...) OT_EVAL5(OT_EVAL5(OT_EVAL5(__VA_ARGS__)))
#define OT_EVAL5(...) __VA_ARGS__

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_ADV_MACROS_H_
