// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_EXAMPLE_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_EXAMPLE_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('e', 'x', 'j')

// clang-format off
/////////////////////////////////////////////////////////////////////////////
// Automatic generation of structs with serialize/deserialize functions:
//
// The follow creates a `struct Foo`:
// typedef struct Foo {
//     int32_t foo;
//     uint32_t bar;
//     char message[20];
// } foo;
// status_t ujson_serialize_foo(ujson_t *context, const foo *self);
// status_t ujson_deserialize_foo(ujson_t *context, foo *self);
#define STRUCT_FOO(field, string) \
    field(foo, int32_t) \
    field(bar, uint32_t) \
    string(message, 20)
UJSON_SERDE_STRUCT(Foo, foo, STRUCT_FOO);

/////////////////////////////////////////////////////////////////////////////
// Automatic generation of structs with serialize/deserialize functions:
//
// The following creates a `struct FooOptional1` with optional fields at end of the struct:
//
// typedef struct FooOptional1 {
//     int32_t foo1;
//     int32_t foo2[2];
//     char message[20];
//     uint8_t has_bar1;
//     uint32_t bar1;
//     uint8_t has_bar2;
//     uint32_t bar2[2];
// } foo_optional_1_t;
// status_t ujson_serialize_foo_optional_1_t(ujson_t *context, const foo_optional_1_t *self);
// status_t ujson_deserialize_foo_optional_1_t(ujson_t *context, foo_optional_1_t *self);
#define STRUCT_FOO_OPTIONAL_1(field, string, field_optional) \
    field(foo1, int32_t) \
    field(foo2, int32_t, 2) \
    string(message, 20) \
    field_optional(bar1, uint32_t) \
    field_optional(bar2, uint32_t, 2)
UJSON_SERDE_STRUCT_OPT_FIELDS(FooOptional1, foo_optional_1_t, STRUCT_FOO_OPTIONAL_1);

/////////////////////////////////////////////////////////////////////////////
// Automatic generation of structs with serialize/deserialize functions:
//
// The following creates a `struct FooOptional2` with optional fields at beginning:
//
// typedef struct FooOptional2 {
//     uint8_t has_bar1;
//     uint32_t bar1;
//     uint8_t has_bar2;
//     uint32_t bar2[2];
//     int32_t foo1;
//     int32_t foo2[2];
//     char message[20];
// } foo_optional_2_t;
// status_t ujson_serialize_foo_optional_2_t(ujson_t *context, const foo_optional_2_t *self);
// status_t ujson_deserialize_foo_optional_2_t(ujson_t *context, foo_optional_2_t *self);
#define STRUCT_FOO_OPTIONAL_2(field, string, field_optional) \
    field_optional(bar1, uint32_t) \
    field_optional(bar2, uint32_t, 2) \
    field(foo1, int32_t) \
    field(foo2, int32_t, 2) \
    string(message, 20)
UJSON_SERDE_STRUCT_OPT_FIELDS(FooOptional2, foo_optional_2_t, STRUCT_FOO_OPTIONAL_2);

/////////////////////////////////////////////////////////////////////////////
// Automatic generation of structs with serialize/deserialize functions:
//
// The following creates a `struct FooOptional3` with optional fields in the middle and non-optional fields in between optional fields
//
// typedef struct FooOptional3 {
//     int32_t foo1;
//     uint8_t has_bar1;
//     uint32_t bar1;
//     int32_t foo2[2];
//     char message[20];
//     uint8_t has_bar2;
//     uint32_t bar2[2];
//     int32_t foo3;
// } foo_optional_3_t;
// status_t ujson_serialize_foo_optional_3_t(ujson_t *context, const foo_optional_3_t *self);
// status_t ujson_deserialize_foo_optional_3_t(ujson_t *context, foo_optional_3_t *self);
#define STRUCT_FOO_OPTIONAL_3(field, string, field_optional) \
    field(foo1, int32_t) \
    field_optional(bar1, uint32_t) \
    field(foo2, int32_t, 2) \
    string(message, 20) \
    field_optional(bar2, uint32_t, 2) \
    field(foo3, int32_t)
UJSON_SERDE_STRUCT_OPT_FIELDS(FooOptional3, foo_optional_3_t, STRUCT_FOO_OPTIONAL_3);

// The next two structs demonstrate struct nesting:
// typedef struct Coord { int32_t x; int32_t y; } coord;
//
// typedef struct Rect {
//     coord top_left;
//     coord bottom_right;
// } rect;
// status_t ujson_serialize_rect(ujson_t *context, const rect *self);
// status_t ujson_deserialize_rect(ujson_t *context, rect *self);
// (and yes: `coord` has serialize and deserialize functions as well).
#define STRUCT_COORD(field, string) \
    field(x, int32_t) \
    field(y, int32_t)
UJSON_SERDE_STRUCT(Coord, coord, STRUCT_COORD);

#define STRUCT_RECT(field, string) \
    field(top_left, coord) \
    field(bottom_right, coord)
UJSON_SERDE_STRUCT(Rect, rect, STRUCT_RECT);

// The next example demonstrates arrays within struct fields:
// struct Matrix {
//     int32_t k[3][5];
// } matrix;
// (and serialize/deserialize functions).
//
// Arrays may have arbitrary dimension.  However, ujson has no concept
// of a variable sized array:
//   - Serialize will always emit _all_ elements.
//   - Deserialize will _not_ initialize absent elements.
#define STRUCT_MATRIX(field, string) \
    field(k, int32_t, 3, 5)
UJSON_SERDE_STRUCT(Matrix, matrix, STRUCT_MATRIX);

/////////////////////////////////////////////////////////////////////////////
// Automatic generation of enums with serialize/deserialize functions:
//
// The following creates an `enum Direction`:
// typedef enum Direction {
//     kDirectionNorth,
//     kDirectionEast,
//     kDirectionSouth,
//     kDirectionWest,
// } direction;
// status_t ujson_serialize_direction(ujson_t *context, const direction *self);
// status_t ujson_deserialize_direction(ujson_t *context, direction *self);
#define ENUM_DIRECTION(_, value) \
    value(_, North) \
    value(_, East) \
    value(_, South) \
    value(_, West)
UJSON_SERDE_ENUM(Direction, direction, ENUM_DIRECTION);

/////////////////////////////////////////////////////////////////////////////
// Automatic generation of C enums corresponding to rust `with_unknown!` enums
//
// The following creates an `enum FuzzyBool`:
// typedef enum FuzzyBool {
//     kFuzzyBoolFalse = 0,
//     FuzzyBoolTrue = 100,
// } fuzzy_bool;
// status_t ujson_serialize_fuzzy_bool(ujson_t *context, const fuzzy_bool *self);
// status_t ujson_deserialize_fuzzy_bool(ujson_t *context, fuzzy_bool *self);
#define ENUM_FUZZY_BOOL(_, value) \
    value(_, False, 0) \
    value(_, True, 100)
C_ONLY(UJSON_SERDE_ENUM(FuzzyBool, fuzzy_bool, ENUM_FUZZY_BOOL, WITH_UNKNOWN));

/////////////////////////////////////////////////////////////////////////////
// Other miscellaneous supported types: bool and status_t
//
// status_t ujson_serialize_misc_t(ujson_t *context, const misc_t *self);
// status_t ujson_deserialize_misc_t(ujson_t *context, misc_t *self);
#define STRUCT_MISC(field, string) \
    field(value, bool) \
    field(status, status_t)
UJSON_SERDE_STRUCT(Misc, misc_t, STRUCT_MISC);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_EXAMPLE_H_
