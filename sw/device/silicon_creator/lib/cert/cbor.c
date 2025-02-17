// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cbor.h"

#include "sw/device/lib/base/memory.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "CBOR library assumes that the system is little endian.");

typedef enum {
  Cbor_Type_Uint = 0,
  Cbor_Type_Sint = 1,
  Cbor_Type_Bstr = 2,
  Cbor_Type_Tstr = 3,
  Cbor_Type_Array = 4,
  Cbor_Type_Map = 5,
} cbor_type_t;

typedef enum {
  Cbor_Arg_Type_U8 = 24,
  Cbor_Arg_Type_U16 = 25,
  Cbor_Arg_Type_U32 = 26,
  Cbor_Arg_Type_U64 = 27,
} cbor_arg_type_t;

size_t cbor_calc_arg_size(const uint64_t value) {
  if (value <= 23) {
    return 0;
  } else if (value <= 0xff) {
    return 1;
  } else if (value <= 0xffff) {
    return 2;
  } else if (value <= 0xffffffff) {
    return 4;
  } else {
    return 8;
  };
}

static uint8_t cbor_calc_additional_info(const uint64_t value) {
  if (value <= 23) {
    return (uint8_t)value;
  } else if (value <= 0xff) {
    return Cbor_Arg_Type_U8;
  } else if (value <= 0xffff) {
    return Cbor_Arg_Type_U16;
  } else if (value <= 0xffffffff) {
    return Cbor_Arg_Type_U32;
  } else {
    return Cbor_Arg_Type_U64;
  };
}

size_t cbor_calc_int_size(const int64_t value) {
  if (value < 0)
    return cbor_calc_arg_size((uint64_t)(-(value + 1)));
  else
    return cbor_calc_arg_size((uint64_t)value);
}

size_t cbor_write_raw_bytes(cbor_out_t *p, const uint8_t *raw,
                            const size_t raw_size) {
  if (p) {
    memcpy(p->start + p->offset, raw, raw_size);
    p->offset += raw_size;
  }

  return raw_size;
}

static size_t cbor_write_type(cbor_out_t *p, cbor_type_t type,
                              const uint64_t arg) {
  const size_t sz = cbor_calc_arg_size(arg);

  if (p) {
    const uint8_t add_info = cbor_calc_additional_info(arg);
    const uint8_t *parg = (uint8_t *)&arg + sz;

    p->start[p->offset++] = ((uint8_t)(type << 5) | add_info);
    for (size_t i = 0; i < sz; ++i)
      p->start[p->offset++] = *(--parg);
  }

  return 1 + sz;
}

size_t cbor_write_int(cbor_out_t *p, const int64_t value) {
  if (value < 0)
    return cbor_write_type(p, Cbor_Type_Sint, (uint64_t)(-(value + 1)));
  else
    return cbor_write_type(p, Cbor_Type_Uint, (uint64_t)value);
}

size_t cbor_write_bstr_header(cbor_out_t *p, const size_t bstr_size) {
  return cbor_write_type(p, Cbor_Type_Bstr, bstr_size);
}

size_t cbor_write_tstr_header(cbor_out_t *p, const size_t tstr_size) {
  return cbor_write_type(p, Cbor_Type_Tstr, tstr_size);
}

size_t cbor_write_array_header(cbor_out_t *p, const size_t num_elements) {
  return cbor_write_type(p, Cbor_Type_Array, num_elements);
}

size_t cbor_write_map_header(cbor_out_t *p, const size_t num_pairs) {
  return cbor_write_type(p, Cbor_Type_Map, num_pairs);
}
