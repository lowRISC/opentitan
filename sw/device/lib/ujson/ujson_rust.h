// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_RUST_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_RUST_H_

// Definitions of the UJSON macros that emit code that can be trivially
// transformed into rust code:
//
// Preprocess the input, grep out all the preprocessor noise,
// translate `rust_attr` into `#` (rust attributes) and finally format the code:
//      gcc -nostdinc -I. -E -DRUST_PREPROCESSOR_EMIT <input_file> \
//          | grep -v '#' \
//          | sed -e "s/rust_attr/#/g" \
//          | rustfmt > output_file

#ifndef RUST_PREPROCESSOR_EMIT
#error "Do not include this file directly.  Include ujson_derive.h instead."
#endif  // RUST_PREPROCESSOR_EMIT
#include "sw/device/lib/base/adv_macros.h"

#define uint64_t u64
#define uint32_t u32
#define uint16_t u16
#define uint8_t u8
#define size_t usize

#define int64_t i64
#define int32_t i32
#define int16_t i16
#define int8_t i8

#define RUST_DEFAULT_DERIVE Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq

// clang-format off
rust_attr[allow(unused_imports)]
use opentitanlib::test_utils::status::status_t;

// clang-format is turned off; as scary as these macros look, they look
// even scarier after clang-format is done with them.
#define ujson_struct_field_array_indirect() ujson_struct_field_array
#define ujson_struct_field_array(t_, sz_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        [t_; sz_]\
    , /*else*/ \
        [OT_OBSTRUCT(ujson_struct_field_array_indirect)()(t_, __VA_ARGS__); sz_] \
    ) /*endif*/

#define ujson_struct_field(name_, type_, ...) \
    pub OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        name_: type_ \
    , /*else*/ \
        name_: OT_EVAL(ujson_struct_field_array(type_, __VA_ARGS__)) \
    ) /*endif*/,

#define ujson_struct_string(name_, size_, ...) \
    ujson_struct_field(name_, String, ##__VA_ARGS__)

#define UJSON_DECLARE_STRUCT(formal_name_, name_, decl_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        rust_attr[derive(RUST_DEFAULT_DERIVE)] /*transform into #[...] */ \
    , /*else*/ \
        rust_attr[derive(__VA_ARGS__)] /*transform into #[...] */ \
    ) /*endif*/ \
    rust_attr[allow(non_camel_case_types)] \
    pub struct name_ { \
        decl_(ujson_struct_field, ujson_struct_string) \
    } \
    rust_attr[allow(dead_code)] \
    pub type formal_name_ = name_ /*eat_semicolon*/

#define ujson_enum_value(formal_name_, name_, ...) \
    pub OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        name_ \
    , /*else*/ \
        name_ = __VA_ARGS__ \
    ) /*endif*/,

#define UJSON_DECLARE_ENUM(formal_name_, name_, decl_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        rust_attr[derive(RUST_DEFAULT_DERIVE)] /*transform into #[...] */ \
    , /*else*/ \
        rust_attr[derive(__VA_ARGS__)] /*transform into #[...] */ \
    ) /*endif*/ \
    rust_attr[repr(u32)] /* transform into #[...] */ \
    rust_attr[allow(non_camel_case_types)] \
    pub enum name_ { \
        decl_(formal_name_, ujson_enum_value) \
        RUST_ENUM_INTVALUE (u32), \
    } \
    rust_attr[allow(dead_code)] \
    pub type formal_name_ = name_ /*eat_semicolon*/
// clang-format on

//////////////////////////////////////////////////////////////////////
// Combined build-everything macro
//////////////////////////////////////////////////////////////////////
#define UJSON_SERDE_STRUCT(formal_name_, name_, decl_, ...) \
  UJSON_DECLARE_STRUCT(formal_name_, name_, decl_, ##__VA_ARGS__)

#define UJSON_SERDE_ENUM(formal_name_, name_, decl_, ...) \
  UJSON_DECLARE_ENUM(formal_name_, name_, decl_, ##__VA_ARGS__)

#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_RUST_H_
