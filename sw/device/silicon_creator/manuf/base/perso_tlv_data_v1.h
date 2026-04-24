// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V1_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V1_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef uint32_t perso_tlv_object_header_v1_t;
typedef uint32_t perso_tlv_cert_header_v1_t;

typedef enum perso_tlv_obj_header_fields_v1 {
  // Object size, total size, this header included.
  kObjhV1SizeFieldShift = 0,
  kObjhV1SizeFieldWidth = 24,
  kObjhV1SizeFieldMask = (1 << kObjhV1SizeFieldWidth) - 1,

  // Object type, one of perso_tlv_object_type_t.
  kObjhV1TypeFieldShift = kObjhV1SizeFieldWidth,
  kObjhV1TypeFieldWidth =
      sizeof(perso_tlv_object_header_v1_t) * 8 - kObjhV1SizeFieldWidth,
  kObjhV1TypeFieldMask = (1 << kObjhV1TypeFieldWidth) - 1,
} perso_tlv_obj_header_fields_v1_t;

typedef enum perso_tlv_cert_header_fields_v1 {
  // Certificate size, total size, this header and name length included.
  kCrthV1SizeFieldShift = 0,
  kCrthV1SizeFieldWidth = 24,
  kCrthV1SizeFieldMask = (1 << kCrthV1SizeFieldWidth) - 1,

  // Length of the certificate name immediately following the header.
  kCrthV1NameSizeFieldShift = kCrthV1SizeFieldWidth,
  kCrthV1NameSizeFieldWidth =
      sizeof(perso_tlv_cert_header_v1_t) * 8 - kCrthV1SizeFieldWidth,
  kCrthV1NameSizeFieldMask = (1 << kCrthV1NameSizeFieldWidth) - 1,
} perso_tlv_cert_header_fields_v1_t;

// Helper macros allowing set or get various object and certificate header
// fields. Operate on objects in big endian representation, as they are
// transferred over wire.
#define PERSO_TLV_SET_FIELD_V1(type_name, field_name, full_value, field_value) \
  {                                                                            \
    uint32_t mask = k##type_name##field_name##FieldMask;                       \
    uint32_t shift = k##type_name##field_name##FieldShift;                     \
    uint32_t fieldv = (uint32_t)(field_value)&mask;                            \
    uint32_t fullv = __builtin_bswap32((uint32_t)(full_value));                \
    mask = (uint32_t)(mask << shift);                                          \
    (full_value) = __builtin_bswap32(                                          \
        (uint32_t)((fullv & ~mask) | (((uint32_t)fieldv) << shift)));          \
  }

#define PERSO_TLV_GET_FIELD_V1(type_name, field_name, full_value, field_value) \
  {                                                                            \
    uint32_t mask = k##type_name##field_name##FieldMask;                       \
    uint32_t shift = k##type_name##field_name##FieldShift;                     \
    *(field_value) = (__builtin_bswap32(full_value) >> shift) & mask;          \
  }

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V1_H_
