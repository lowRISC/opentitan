// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_DERIVE_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_DERIVE_H_
// This is what we'll use as the Rust enumeration name for C-enum values
// that do not have a symbolic name.
#define RUST_ENUM_INTVALUE IntValue

#ifndef RUST_PREPROCESSOR_EMIT
#include <stdint.h>

#include "sw/device/lib/base/adv_macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

#define RUST_ENUM_INTVALUE_STR OT_STRINGIFY(RUST_ENUM_INTVALUE)
// clang-format off
// clang-format is turned off; as scary as these macros look, they look
// even scarier after clang-format is done with them.
#define ujson_struct_field_array_indirect() ujson_struct_field_array
#define ujson_struct_field_array(nt_, sz_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        nt_[sz_] \
    , /*else*/ \
        OT_OBSTRUCT(ujson_struct_field_array_indirect)()(nt_[sz_], __VA_ARGS__) \
    ) /*endif*/

#define ujson_struct_field(name_, type_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        type_ name_; \
    , /*else*/ \
        OT_EVAL(ujson_struct_field_array(type_ name_, __VA_ARGS__)); \
    ) /*endif*/

#define ujson_struct_string(name_, size_, ...) \
    ujson_struct_field(name_, char, ##__VA_ARGS__, size_)

#define UJSON_DECLARE_STRUCT(formal_name_, name_, decl_, ...) \
    typedef struct formal_name_ { \
        decl_(ujson_struct_field, ujson_struct_string) \
    } name_

#define ujson_enum_value(formal_name_, name_, ...) \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        k ##formal_name_ ## name_ \
    , /*else*/ \
        k ##formal_name_ ## name_ = __VA_ARGS__ \
    ) /*endif*/ ,

#define UJSON_DECLARE_ENUM(formal_name_, name_, decl_, ...) \
    typedef enum formal_name_ { \
        decl_(formal_name_, ujson_enum_value) \
    } name_

#ifdef UJSON_SERDE_IMPL

// Helper to count number of fields.
#define ujson_count(name_, type_, ...) +1

//////////////////////////////////////////////////////////////////////
// Serialize Implementation
//////////////////////////////////////////////////////////////////////
#define ujson_ser_loop_indirect() ujson_ser_loop
#define ujson_ser_loop(expr, count, ...) \
    TRY(ujson_putbuf(uj, "[", 1)); \
    for(size_t x=0; x < count; ++x) { \
        if (x) TRY(ujson_putbuf(uj, ",", 1)); \
        OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
        ( /*then*/ \
            expr; \
        , /*else*/ \
            OT_OBSTRUCT(ujson_ser_loop_indirect)()(expr, __VA_ARGS__) \
        ) /*endif*/ \
    } \
    TRY(ujson_putbuf(uj, "]", 1));

#define ujson_ser_field(name_, type_, ...) { \
        TRY(ujson_serialize_string(uj, #name_)); \
        TRY(ujson_putbuf(uj, ":", 1)); \
        OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
        ( /*then*/ \
            TRY(ujson_serialize_##type_(uj, &self->name_)); \
        , /*else*/ \
            const type_ *p = (const type_*)self->name_; \
            OT_EVAL(ujson_ser_loop( \
                    TRY(ujson_serialize_##type_(uj, p++)), __VA_ARGS__)) \
        ) /*endif*/ \
        if (--nfield) TRY(ujson_putbuf(uj, ",", 1)); \
    }

#define ujson_ser_string(name_, size_, ...) { \
        TRY(ujson_serialize_string(uj, #name_)); \
        TRY(ujson_putbuf(uj, ":", 1)); \
        OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
        ( /*then*/ \
            TRY(ujson_serialize_string(uj, self->name_)); \
        , /*else*/ \
            const char *p = (const char*)self->name_; \
            OT_EVAL(ujson_ser_loop( \
                    TRY(ujson_serialize_string(uj, p)); p+=size_, __VA_ARGS__)) \
        ) /*endif*/ \
        if (--nfield) TRY(ujson_putbuf(uj, ",", 1)); \
    }

#define UJSON_SERIALIZE_STRUCT(name_, decl_) \
    status_t ujson_serialize_##name_(ujson_t *uj, const name_ *self) { \
        size_t nfield = decl_(ujson_count, ujson_count); \
        TRY(ujson_putbuf(uj, "{", 1)); \
        decl_(ujson_ser_field, ujson_ser_string) \
        TRY(ujson_putbuf(uj, "}", 1)); \
        return OK_STATUS(); \
    } \
    extern const int __never_referenced___here_to_eat_a_semicolon[]

#define ujson_ser_enum(formal_name_, name_, ...) \
    case k ##formal_name_ ## name_: \
        TRY(ujson_serialize_string(uj, #name_)); break;

#define UJSON_SERIALIZE_ENUM(formal_name_, name_, decl_) \
    status_t ujson_serialize_##name_(ujson_t *uj, const name_ *self) { \
        switch(*self) { \
            decl_(formal_name_, ujson_ser_enum) \
            default: \
                TRY(ujson_putbuf(uj, \
                    "{\"" RUST_ENUM_INTVALUE_STR "\":", \
                    sizeof("{\"" RUST_ENUM_INTVALUE_STR "\":") - 1)); \
                TRY(ujson_serialize_uint32_t(uj, (const uint32_t*)self)); \
                TRY(ujson_putbuf(uj, "}", 1)); \
        } \
        return OK_STATUS(); \
    } \
    extern const int __never_referenced___here_to_eat_a_semicolon[]

//////////////////////////////////////////////////////////////////////
// Deserialize Implementation
//////////////////////////////////////////////////////////////////////
#define ujson_de_loop_indirect() ujson_de_loop
#define ujson_de_loop(mult, expr, count, ...) \
    TRY(ujson_consume(uj, '[')); \
    OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
    ( /*then*/ \
        size_t i = 0; \
        while(true) { \
            if (TRY(ujson_consume_maybe(uj, ']'))) break; \
            if (i) TRY(ujson_consume(uj, ',')); \
            if (i < count) {  expr; ++i; } \
        } \
        if (i < count) { p += (count - i) * mult; } \
    , /*else*/ \
        for(size_t x=0;; ++x) { \
            if (TRY(ujson_consume_maybe(uj, ']'))) break; \
            if (x) TRY(ujson_consume(uj, ',')); \
            OT_OBSTRUCT(ujson_de_loop_indirect)()(mult, expr, __VA_ARGS__) \
        } \
    ) /*endif*/ \

#define ujson_de_field(name_, type_, ...) \
    else if (ujson_streq(key, #name_)) { \
        OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
        ( /*then*/ \
            TRY(ujson_deserialize_##type_(uj, &self->name_)); \
        , /*else*/ \
            type_ *p = (type_*)self->name_; \
            OT_EVAL(ujson_de_loop(1, \
                TRY(ujson_deserialize_##type_(uj, p++)), __VA_ARGS__)) \
        ) /*endif*/ \
    }

#define ujson_de_string(name_, size_, ...) \
    else if (ujson_streq(key, #name_)) { \
        OT_IIF(OT_NOT(OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__))) \
        ( /*then*/ \
            TRY(ujson_parse_qs(uj, self->name_, sizeof(self->name_))); \
        , /*else*/ \
            char *p = (char*)self->name_; \
            OT_EVAL(ujson_de_loop(size_, \
                TRY(ujson_parse_qs(uj, p, sizeof(self->name_))); p+=size_, __VA_ARGS__)) \
        ) /*endif*/ \
    }

#define UJSON_DESERIALIZE_STRUCT(name_, decl_) \
    status_t ujson_deserialize_##name_(ujson_t *uj, name_ *self) { \
        size_t nfield = 0; \
        char key[128]; \
        TRY(ujson_consume(uj, '{')); \
        while(TRY(ujson_consume_maybe(uj, '}')) == 0) { \
            if (nfield++ > 0) { \
                TRY(ujson_consume(uj, ',')); \
            } \
            TRY(ujson_parse_qs(uj, key, sizeof(key))); \
            TRY(ujson_consume(uj, ':')); \
            if (0) {} \
            decl_(ujson_de_field, ujson_de_string) \
            else { \
                return INVALID_ARGUMENT(); \
            } \
        } \
        return OK_STATUS(); \
    } \
    extern const int __never_referenced___here_to_eat_a_semicolon[]

#define ujson_de_enum(formal_name_, name_, ...) \
    else if (ujson_streq(value, #name_)) { *self = k ##formal_name_ ## name_; }

#define UJSON_DESERIALIZE_ENUM(formal_name_, name_, decl_) \
    status_t ujson_deserialize_##name_(ujson_t *uj, name_ *self) { \
        char value[128]; \
        if (TRY(ujson_consume_maybe(uj, '"'))) { \
            TRY(ujson_ungetc(uj, '"')); \
            TRY(ujson_parse_qs(uj, value, sizeof(value))); \
            if (0) {} \
            decl_(formal_name_, ujson_de_enum) \
            else { \
                return INVALID_ARGUMENT(); \
            } \
        } else { \
            TRY(ujson_consume(uj, '{')); \
            TRY(ujson_parse_qs(uj, value, sizeof(value))); \
            TRY(ujson_consume(uj, ':')); \
            if (ujson_streq(value, RUST_ENUM_INTVALUE_STR)) { \
                TRY(ujson_deserialize_uint32_t(uj, (uint32_t*)self)); \
            } else { \
                return INVALID_ARGUMENT(); \
            } \
            TRY(ujson_consume(uj, '}')); \
        } \
        return OK_STATUS(); \
    } \
    extern const int __never_referenced___here_to_eat_a_semicolon[]
// clang-format on
#else  // UJSON_SERDE_IMPL
#define UJSON_SERIALIZE_STRUCT(name_, decl_) \
  status_t ujson_serialize_##name_(ujson_t *uj, const name_ *self)
#define UJSON_SERIALIZE_ENUM(formal_name_, name_, decl_) \
  status_t ujson_serialize_##name_(ujson_t *uj, const name_ *self)

#define UJSON_DESERIALIZE_STRUCT(name_, decl_) \
  status_t ujson_deserialize_##name_(ujson_t *uj, name_ *self);
#define UJSON_DESERIALIZE_ENUM(formal_name_, name_, decl_) \
  status_t ujson_deserialize_##name_(ujson_t *uj, name_ *self);

#endif  // UJSON_SERDE_IMPL
//////////////////////////////////////////////////////////////////////
// Combined build-everything macros
//////////////////////////////////////////////////////////////////////
#define UJSON_SERDE_STRUCT(formal_name_, name_, decl_, ...)        \
  UJSON_DECLARE_STRUCT(formal_name_, name_, decl_, ##__VA_ARGS__); \
  UJSON_SERIALIZE_STRUCT(name_, decl_);                            \
  UJSON_DESERIALIZE_STRUCT(name_, decl_)

#define UJSON_SERDE_ENUM(formal_name_, name_, decl_, ...)        \
  UJSON_DECLARE_ENUM(formal_name_, name_, decl_, ##__VA_ARGS__); \
  UJSON_SERIALIZE_ENUM(formal_name_, name_, decl_);              \
  UJSON_DESERIALIZE_ENUM(formal_name_, name_, decl_)

#else  // RUST_PREPROCESSOR_EMIT
#include "sw/device/lib/ujson/ujson_rust.h"
#endif  // RUST_PREPROCESSOR_EMIT
#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_DERIVE_H_
