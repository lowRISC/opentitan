// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_INTERNAL_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_INTERNAL_STATUS_H_

#ifndef USING_INTERNAL_STATUS
#error "Do not include internal/status.h directly. Include status.h instead."
#endif
#include "sw/device/lib/base/bitfield.h"

#define USING_ABSL_STATUS
#include "sw/device/lib/base/internal/absl_status.h"
#undef USING_ABSL_STATUS
#ifdef __cplusplus
extern "C" {
#endif

/**
 * We use the error category codes from absl_status.h.  We build a packed
 * status value that identifies the source of the error (in the form of the
 * module identifier and line number).
 *
 * By default, the module identifier is the first three letters of the
 * source filename.  The identifier can be overridden (per-module) with the
 * DECLARE_MODULE_ID macro.
 *
 * Our status codes are arranged as a packed bitfield, with the sign
 * bit signifying whether the value represents a result or an error.
 *
 * All Ok (good) values:
 *     31                                             0
 *  +---+---------------------------------------------+
 *  |   |                  31 bit                     |
 *  | 0 |                  Result                     |
 *  +---+---------------------------------------------+
 *
 * All Error values:
 *     31      26      21      16             5       0
 *  +---+-------+-------+-------+-------------+-------+
 *  |   |   15 bit              | 11 bit      | 5 bit |
 *  | 1 |   Module Identifier   | Line Number | code  |
 *  +---+-------+-------+-------+-------------+-------+
 *
 * The module identifier value is interpreted as three 5-bit fields
 * representing the characters [0x40..0x5F] (e.g. [@ABC ... _]).
 */

#define STATUS_FIELD_CODE ((bitfield_field32_t){.mask = 0x1f, .index = 0})
#define STATUS_FIELD_ARG ((bitfield_field32_t){.mask = 0x7ff, .index = 5})
#define STATUS_FIELD_MODULE_ID \
  ((bitfield_field32_t){.mask = 0x7fff, .index = 16})
#define STATUS_BIT_ERROR 31

/*
 * Creates a module ID from 3 ASCII characters.
 *
 * To declare a module-id in one of your own files:
 * #define MODULE_ID MAKE_MODULE_ID('a', 'b', 'c')
 */
#define MAKE_MODULE_ID(a, b, c) \
  (uint32_t)(((((a)&0xff) << 16) | (((b)&0xff) << 8) | ((c)&0xff)))

static inline uint8_t __status_ascii_5bit(uint8_t c) {
  if (c >= '@' && c <= '_') {
    return c - '@';
  } else if (c >= '`' && c <= 'z') {
    return c - '`';
  } else {
    return '_' - '@';
  }
}

/** Encode a module ID created by MAKE_MODULE_ID.
 *
 * The resulting encoding is a 15 bit value which can be put inside the
 * STATUS_FIELD_MODULE_ID.
 *
 * @param module_id Module ID created by MAKE_MODULE_ID.
 * @return Encoding suitable for use inside the Module Identifier field of
 * status_t.
 */
static inline uint32_t status_encode_module_id(uint32_t module_id) {
  return (uint32_t)__status_ascii_5bit((uint8_t)(module_id >> 16)) |
         ((uint32_t)__status_ascii_5bit((uint8_t)(module_id >> 8)) << 5) |
         ((uint32_t)__status_ascii_5bit((uint8_t)module_id) << 10);
}

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_INTERNAL_STATUS_H_
