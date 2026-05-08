// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V0_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V0_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef uint16_t perso_tlv_object_header_v0_t;
typedef uint16_t perso_tlv_cert_header_v0_t;

typedef enum perso_tlv_obj_header_fields_v0 {
  // Object size, total size, this header included.
  kObjhSizeFieldShiftV0 = 0,
  kObjhSizeFieldWidthV0 = 12,
  kObjhSizeFieldMaskV0 = (1 << kObjhSizeFieldWidthV0) - 1,

  // Object type, one of perso_tlv_object_type_t.
  kObjhTypeFieldShiftV0 = kObjhSizeFieldWidthV0,
  kObjhTypeFieldWidthV0 =
      sizeof(perso_tlv_object_header_v0_t) * 8 - kObjhSizeFieldWidthV0,
  kObjhTypeFieldMaskV0 = (1 << kObjhTypeFieldWidthV0) - 1,
} perso_tlv_obj_header_fields_v0_t;

typedef enum perso_tlv_cert_header_fields_v0 {
  // Certificate size, total size, this header and name length included.
  kCrthSizeFieldShiftV0 = 0,
  kCrthSizeFieldWidthV0 = 12,
  kCrthSizeFieldMaskV0 = (1 << kCrthSizeFieldWidthV0) - 1,

  // Length of the certificate name immediately following the header.
  kCrthNameSizeFieldShiftV0 = kCrthSizeFieldWidthV0,
  kCrthNameSizeFieldWidthV0 =
      sizeof(perso_tlv_cert_header_v0_t) * 8 - kCrthSizeFieldWidthV0,
  kCrthNameSizeFieldMaskV0 = (1 << kCrthNameSizeFieldWidthV0) - 1,
} perso_tlv_cert_header_fields_v0_t;

// Helper macros allowing set or get various object and certificate header
// fields. Operate on objects in big endian representation, as they are
// transferred over wire.
#define PERSO_TLV_SET_FIELD(type_name, field_name, full_value, field_value) \
  {                                                                         \
    uint16_t mask = k##type_name##field_name##FieldMask;                    \
    uint16_t shift = k##type_name##field_name##FieldShift;                  \
    uint16_t fieldv = (uint16_t)(field_value)&mask;                         \
    uint16_t fullv = __builtin_bswap16((uint16_t)(full_value));             \
    mask = (uint16_t)(mask << shift);                                       \
    (full_value) = __builtin_bswap16(                                       \
        (uint16_t)((fullv & ~mask) | (((uint16_t)fieldv) << shift)));       \
  }

#define PERSO_TLV_GET_FIELD(type_name, field_name, full_value, field_value) \
  {                                                                         \
    uint16_t mask = k##type_name##field_name##FieldMask;                    \
    uint16_t shift = k##type_name##field_name##FieldShift;                  \
    *(field_value) = (__builtin_bswap16(full_value) >> shift) & mask;       \
  }

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_V0_H_
