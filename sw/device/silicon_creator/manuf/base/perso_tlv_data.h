// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/provisioning_data.h"

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
} perso_tlv_object_type_t;

typedef uint16_t perso_tlv_object_header_t;
typedef uint16_t perso_tlv_cert_header_t;
typedef uint16_t perso_tlv_dev_seed_header_t;

typedef enum perso_tlv_obj_header_fields {
  // Object size, total size, this header included.
  kObjhSizeFieldShift = 0,
  kObjhSizeFieldWidth = 12,
  kObjhSizeFieldMask = (1 << kObjhSizeFieldWidth) - 1,

  // Object type, one of perso_tlv_object_types_t.
  kObjhTypeFieldShift = kObjhSizeFieldWidth,
  kObjhTypeFieldWidth =
      sizeof(perso_tlv_object_header_t) * 8 - kObjhSizeFieldWidth,
  kObjhTypeFieldMask = (1 << kObjhTypeFieldWidth) - 1,
} perso_tlv_obj_header_fields_t;

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

// Helper macros allowing set or get various header fields.
#define PERSO_TLV_SET_FIELD(type_name, field_name, full_value, field_value)   \
  {                                                                           \
    uint16_t mask = k##type_name##field_name##FieldMask;                      \
    uint16_t shift = k##type_name##field_name##FieldShift;                    \
    uint16_t fieldv = (uint16_t)field_value;                                  \
    uint16_t fullv = (uint16_t)full_value;                                    \
    fieldv = field_value & mask;                                              \
    mask = (uint16_t)(mask << shift);                                         \
    full_value = (uint16_t)((fullv & ~mask) | (((uint16_t)fieldv) << shift)); \
  }

#define PERSO_TLV_GET_FIELD(type_name, field_name, full_value, field_value) \
  {                                                                         \
    uint16_t mask = k##type_name##field_name##FieldMask;                    \
    uint16_t shift = k##type_name##field_name##FieldShift;                  \
    *field_value = (full_value >> shift) & mask;                            \
  }

/**
 * A helper structure for quick access to a certificate stored as a perso LTV
 * object.
 **/
typedef struct perso_tlv_cert_block {
  size_t obj_size;
  size_t wrapped_cert_size;
  const void *wrapped_cert_p;
  char name[kCrthNameSizeFieldMask + 1];
} perso_tlv_cert_block_t;

/**
 *  Given the pointer to an LTV object, in case this is an endorsed certificate
 *  set up the perso_tlv_cert_block_t structure for it.
 *
 * @param buf pointer to the LTV object storing the certificate
 * @param max_room total number of bytes til the end of the buffer (the LTV
 *               object is likely to be smaller, but can't be any bigger)
 * @param[out] block pointer to the block to set up.
 *
 * @return OK_STATUS on success, NOT_FOUND if the object is not an endorsed
 *              certificate, or the error condition encountered.
 */
status_t perso_tlv_set_cert_block(const uint8_t *buf, size_t max_room,
                                  perso_tlv_cert_block_t *block);

/**
 * Wrap the passed in certificate in a perso LTV object and copy it into the
 * body of the perso_blob.
 *
 * @param name the name of the certificate
 * @param needs_endorsement defines the type of the LTV object the certificate
 *              is wrapped into
 * @param cert_body the actual certificate
 * @param cert_size size of the certificate in bytes
 * @param[out] perso_blob container for sending data to host.
 *
 * @return status of the operation.
 */
status_t perso_tlv_prepare_cert_for_shipping(const char *name,
                                             bool needs_endorsement,
                                             const void *cert_body,
                                             size_t cert_size,
                                             perso_blob_t *perso_blob);

/**
 * A helper function adding arbitrary amount of data to the body of a perso
 * blob.
 *
 * @param data ponter to the data to add to the blob
 * @param size number of bytes of data
 * @param perso_blob pointer to the blob to add data to
 *
 * @return status of the operation.
 */
status_t perso_tlv_push_to_blob(const void *data, size_t size,
                                perso_blob_t *perso_blob);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSO_TLV_DATA_H_
