// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/error.h"

/**
 * Personalization data is sent between the device and the host during the
 * device provisioning. Personalization data is laid out as a sequence of
 * concatenated LTV objects. The length and type field of the objects are packed
 * in a 16 bit integer:
 *  d15                                           d0
 *  +-------------+--------------------------------+
 *  | 4 bit type  |   12 bits total  object size   |
 *  +-------------+--------------------------------+
 *
 * The following object types have been defined so far:
 */
typedef enum perso_tlv_object_type {
  kPersoObjectTypeX509Tbs = 0,
  kPersoObjectTypeX509Cert = 1,
  kPersoObjectTypeDevSeed = 2,
  kPersoObjectTypeCwtCert = 3,
} perso_tlv_object_type_t;

typedef uint16_t perso_tlv_object_header_t;
typedef uint16_t perso_tlv_cert_header_t;
typedef uint16_t perso_tlv_dev_seed_header_t;

typedef enum perso_tlv_obj_header_fields {
  // Object size, total size, this header included.
  kObjhSizeFieldShift = 0,
  kObjhSizeFieldWidth = 12,
  kObjhSizeFieldMask = (1 << kObjhSizeFieldWidth) - 1,

  // Object type, one of perso_tlv_object_type_t.
  kObjhTypeFieldShift = kObjhSizeFieldWidth,
  kObjhTypeFieldWidth =
      sizeof(perso_tlv_object_header_t) * 8 - kObjhSizeFieldWidth,
  kObjhTypeFieldMask = (1 << kObjhTypeFieldWidth) - 1,
} perso_tlv_obj_header_fields_t;

typedef struct perso_tlv_dev_seed_element {
  uint32_t el[8];
} perso_tlv_dev_seed_element_t;

typedef struct perso_tlv_dev_seed {
  perso_tlv_dev_seed_element_t key;
  perso_tlv_dev_seed_element_t context;
} perso_tlv_dev_seed_t;

typedef struct perso_tlv_dev_seed_set {
  perso_tlv_dev_seed_t seeds[2];
} perso_tlv_dev_seed_set_t;

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
typedef enum perso_tlv_cert_header_fields {
  // Certificate size, total size, this header and name length included.
  kCrthSizeFieldShift = 0,
  kCrthSizeFieldWidth = 12,
  kCrthSizeFieldMask = (1 << kCrthSizeFieldWidth) - 1,

  // Length of the certificate name immediately following the header.
  kCrthNameSizeFieldShift = kCrthSizeFieldWidth,
  kCrthNameSizeFieldWidth =
      sizeof(perso_tlv_cert_header_t) * 8 - kCrthSizeFieldWidth,
  kCrthNameSizeFieldMask = (1 << kCrthNameSizeFieldWidth) - 1,
} perso_tlv_cert_header_fields_t;

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

/**
 * A helper structure for quick access to a certificate stored as a perso LTV
 * object.
 */
typedef struct perso_tlv_cert_obj {
  /**
   * Pointer to the start of the perso LTV object.
   */
  uint8_t *obj_p;
  /**
   * LTV object size (in bytes).
   */
  size_t obj_size;
  /**
   * LTV object type.
   */
  uint32_t obj_type;
  /**
   * Pointer to the start of the certificate body (i.e., ASN.1 object for X.509
   * certificates, or CBOR object for CWT certificates).
   */
  uint8_t *cert_body_p;
  /**
   * Certificate (ASN.1 or CBOR) body size (in bytes).
   *
   * Equal to: obj_size - obj_hdr_size - cert_hdr_size - cert_name_len
   */
  size_t cert_body_size;
  /**
   * Certificate name string.
   */
  char name[kCrthNameSizeFieldMask + 1];
} perso_tlv_cert_obj_t;

/**
 * Given the pointer to an LTV object, in case this is an endorsed certificate
 * set up the perso_tlv_cert_obj_t structure for it.
 *
 * @param buf Pointer to the LTV object buffer storing the certificate object.
 * @param ltv_buf_size Total number of bytes until the end of the LTV buffer
 *                     (cert LTV object must be <= the buffer size).
 * @param[out] obj Pointer to the certificate perso LTV object to populate.
 *
 * @return OK_STATUS on success, NOT_FOUND if the object is not an endorsed
 *                   certificate, or the error condition encountered.
 */
OT_WARN_UNUSED_RESULT
rom_error_t perso_tlv_get_cert_obj(uint8_t *buf, size_t ltv_buf_size,
                                   perso_tlv_cert_obj_t *obj);

/**
 * Wraps the passed certificate in a perso LTV object and copies it to an output
 * buffer.
 *
 * The certificate perso LTV object is laid out as follows:
 * - 16 bit LTV object header
 * - 16 bit cert header
 * - Certificate name string
 * - Cerificate data
 *
 * Note that both certificate and object headers' are 16 bit integers in big
 * endian format.
 *
 *  d15                                         d0
 * +-------------+--------------------------------+
 * | 4 bit type  |   12 bits total object size    | <-- Object Header
 * +-------------+--------------------------------+
 * | name length |12 bits total cert payload size | <-- Cert Header
 * +-------------+--------------------------------+
 * |             cert name string                 |
 * +----------------------------------------------+
 * |                   cert                       |
 * +----------------------------------------------+
 *
 * @param name The name of the certificate.
 * @param obj_type The object type that needs to encoded.
 * @param cert The binary certificate blob.
 * @param cert_size Size of the certificate blob in bytes.
 * @param[out] buf Output buffer to copy the data into.
 * @param[inout] buf_size Input is size of the output buffer in bytes; output is
 *                        space of buffer that was consumed by the LTV object.
 * @return status of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t perso_tlv_cert_obj_build(const char *name,
                                     const perso_tlv_object_type_t obj_type,
                                     const uint8_t *cert, size_t cert_size,
                                     uint8_t *buf, size_t *buf_size);

/**
 * Constructs an certificate perso LTV object (shown above) by invoking
 * `perso_tlv_cert_obj_build()` and pushes it to a `perso_blob_t` object used
 * for shuffling data between the host and device during personalization.
 *
 * @param name The name of the certificate.
 * @param needs_endorsement Defines the type of the LTV object the certificate
 *                          is wrapped into (TBS or fully formed).
 * @param cert_format The format of the certificate.
 * @param cert The binary certificate blob.
 * @param cert_size Size of the certificate blob in bytes.
 * @param perso_blob Pointer to the `perso_blob_t` to copy the object to.
 * @return status of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t perso_tlv_push_cert_to_perso_blob(
    const char *name, bool needs_endorsement,
    const dice_cert_format_t cert_format, const uint8_t *cert, size_t cert_size,
    perso_blob_t *pb);

/**
 * Pushes arbitrary data to the perso blob that is sent between host and device.
 *
 * @param data Pointer to the data to add to the blob.
 * @param size Size of the data to add in bytes.
 * @param perso_blob Pointer to the perso blob to add the data to.
 * @return status of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t perso_tlv_push_to_perso_blob(const void *data, size_t size,
                                         perso_blob_t *perso_blob);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
