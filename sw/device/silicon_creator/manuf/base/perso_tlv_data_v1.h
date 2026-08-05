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
  kObjhSizeFieldShiftV1 = 0,
  kObjhSizeFieldWidthV1 = 24,
  kObjhSizeFieldMaskV1 = (1 << kObjhSizeFieldWidthV1) - 1,

  // Object type, one of perso_tlv_object_type_t.
  kObjhTypeFieldShiftV1 = kObjhSizeFieldWidthV1,
  kObjhTypeFieldWidthV1 =
      sizeof(perso_tlv_object_header_v1_t) * 8 - kObjhSizeFieldWidthV1,
  kObjhTypeFieldMaskV1 = (1 << kObjhTypeFieldWidthV1) - 1,
} perso_tlv_obj_header_fields_v1_t;

typedef enum perso_tlv_cert_header_fields_v1 {
  // Certificate size, total size, this header and name length included.
  kCrthSizeFieldShiftV1 = 0,
  kCrthSizeFieldWidthV1 = 24,
  kCrthSizeFieldMaskV1 = (1 << kCrthSizeFieldWidthV1) - 1,

  // Length of the certificate name immediately following the header.
  kCrthNameSizeFieldShiftV1 = kCrthSizeFieldWidthV1,
  kCrthNameSizeFieldWidthV1 =
      sizeof(perso_tlv_cert_header_v1_t) * 8 - kCrthSizeFieldWidthV1,
  kCrthNameSizeFieldMaskV1 = (1 << kCrthNameSizeFieldWidthV1) - 1,
} perso_tlv_cert_header_fields_v1_t;

// Helper macros allowing set or get various object and certificate header
// fields. Operate on objects in big endian representation, as they are
// transferred over wire.
#define PERSO_TLV_SET_FIELD_V1(type_name, field_name, full_value, field_value) \
  {                                                                            \
    uint32_t mask = k##type_name##field_name##FieldMaskV1;                     \
    uint32_t shift = k##type_name##field_name##FieldShiftV1;                   \
    uint32_t fieldv = (uint32_t)(field_value)&mask;                            \
    uint32_t fullv = __builtin_bswap32((uint32_t)(full_value));                \
    mask = (uint32_t)(mask << shift);                                          \
    (full_value) = __builtin_bswap32(                                          \
        (uint32_t)((fullv & ~mask) | (((uint32_t)fieldv) << shift)));          \
  }

#define PERSO_TLV_GET_FIELD_V1(type_name, field_name, full_value, field_value) \
  {                                                                            \
    uint32_t mask = k##type_name##field_name##FieldMaskV1;                     \
    uint32_t shift = k##type_name##field_name##FieldShiftV1;                   \
    *(field_value) = (__builtin_bswap32(full_value) >> shift) & mask;          \
  }

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V1_H_
