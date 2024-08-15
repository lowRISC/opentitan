// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_

#include <stdint.h>

/**
 * Personalization data is sent between the device and the host during the
 * device provision. Personalization data is laid out as a sequence of
 * concatenated LTV objects. The length and type field of the objects are packed
 * in a 16 bit integer:
 *  d15                                           d0
 *  +-------------+--------------------------------+
 *  | 4 bit type  |   12 bits total  object size   |
 *  +-------------+--------------------------------+
 *
 * The following object types have been defined so far:
 */
typedef enum perso_object_type {
  kPersoObjectTypeX509Tbs = 0,
  kPersoObjectTypeX509Cert = 1,
  kPersoObjectTypeDevSeed = 2,
} perso_object_type_t;

typedef uint16_t object_header_t;
typedef uint16_t cert_header_t;
typedef uint16_t dev_seed_header_t;

typedef enum obj_header_fields {
  // Object size, total size, this header included.
  kObjhSizeFieldShift = 0,
  kObjhSizeFieldWidth = 12,
  kObjhSizeFieldMask = (1 << kObjhSizeFieldWidth) - 1,

  // Object type, one of perso_object_types_t.
  kObjhTypeFieldShift = kObjhSizeFieldWidth,
  kObjhTypeFieldWidth = sizeof(object_header_t) * 8 - kObjhSizeFieldWidth,
  kObjhTypeFieldMask = (1 << kObjhTypeFieldWidth) - 1,
} obj_header_fields_t;

/**
 * The x509 certificate is prepended by a 16 bits header followed by the ASCII
 * characters of the certificate name, followed by the certificate body.
 *
 * The certificate header includes 4 bits for the certificate name length then
 * the full size of the certificate object (header size + name length +
 * certificate size).
 *
 *  d15                                           d0
 *  +-------------+--------------------------------+
 *  | 4 bit length|       12 bits total size       |
 *  +-------------+--------------------------------+
 */
typedef enum cert_header_fields {
  // Certificate size, total size, this header and name length included.
  kCrthSizeFieldShift = 0,
  kCrthSizeFieldWidth = 12,
  kCrthSizeFieldMask = (1 << kCrthSizeFieldWidth) - 1,

  // Length of the certificate name immediately following the header.
  kCrthNameSizeFieldShift = kCrthSizeFieldWidth,
  kCrthNameSizeFieldWidth = sizeof(cert_header_t) * 8 - kCrthSizeFieldWidth,
  kCrthNameSizeFieldMask = (1 << kCrthNameSizeFieldWidth) - 1,
} cert_header_fields_t;

// Helper macros allowing set or get various header fields.
#define set_field(type_name, field_name, full_value, field_value)             \
  {                                                                           \
    uint16_t mask = k##type_name##field_name##FieldMask;                      \
    uint16_t shift = k##type_name##field_name##FieldShift;                    \
    uint16_t fieldv = (uint16_t)field_value;                                  \
    uint16_t fullv = (uint16_t)full_value;                                    \
    fieldv = field_value & mask;                                              \
    mask = (uint16_t)(mask << shift);                                         \
    full_value = (uint16_t)((fullv & ~mask) | (((uint16_t)fieldv) << shift)); \
  }

#define get_field(type_name, field_name, full_value, field_value) \
  {                                                               \
    uint16_t mask = k##type_name##field_name##FieldMask;          \
    uint16_t shift = k##type_name##field_name##FieldShift;        \
    *field_value = (full_value >> shift) & mask;                  \
  }
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
