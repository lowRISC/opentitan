// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"

/**
 * A helper function adding arbitrary amount of data to the body of the perso
 * blob, returns error if the passed in data would not fit.
 */
status_t perso_tlv_push_to_blob(const void *data, size_t size,
                                perso_blob_t *perso_blob) {
  size_t room = sizeof(perso_blob->body) - perso_blob->next_free;
  if (room < size)
    return RESOURCE_EXHAUSTED();

  memcpy(perso_blob->body + perso_blob->next_free, data, size);
  perso_blob->next_free += size;

  return OK_STATUS();
}

status_t perso_tlv_set_cert_block(const uint8_t *buf, size_t max_room,
                                  perso_tlv_cert_block_t *block) {
  perso_tlv_object_header_t objh;
  uint16_t obj_size;
  perso_tlv_object_type_t obj_type;
  perso_tlv_cert_header_t crth;
  uint16_t wrapped_cert_size;
  uint16_t name_len;

  memcpy(&objh, buf, sizeof(perso_tlv_object_header_t));
  PERSO_TLV_GET_FIELD(Objh, Size, objh, &obj_size);

  if (obj_size > max_room)
    return INTERNAL();  // Something is really screwed up.
  block->obj_size = obj_size;

  PERSO_TLV_GET_FIELD(Objh, Type, objh, &obj_type);
  if (obj_type != kPersoObjectTypeX509Cert) {
    LOG_INFO("Skipping object of type %d", obj_type);
    return NOT_FOUND();
  }

  // Let's retrieve cert wrapper header.
  const uint8_t *cert_header_start = buf + sizeof(objh);
  memcpy(&crth, cert_header_start, sizeof(perso_tlv_cert_header_t));
  PERSO_TLV_GET_FIELD(Crth, Size, crth, &wrapped_cert_size);
  PERSO_TLV_GET_FIELD(Crth, NameSize, crth, &name_len);

  const size_t min_header_size = sizeof(objh) + sizeof(crth);

  // At least 8 bytes in the certificate body to get its size.
  if ((wrapped_cert_size < (name_len + min_header_size + 8)) ||
      (wrapped_cert_size > max_room))
    return INTERNAL();  // Something is really screwed up.
  block->wrapped_cert_size = wrapped_cert_size;
  block->wrapped_cert_p = buf;

  const uint8_t *name_start = cert_header_start + sizeof(crth);
  memcpy(block->name, name_start, name_len);
  block->name[name_len] = '\0';

  return OK_STATUS();
}

status_t perso_tlv_prepare_cert_for_shipping(const char *name,
                                             bool needs_endorsement,
                                             const void *cert_body,
                                             size_t cert_size,
                                             perso_blob_t *pb) {
  /**
   * * The certificate is laid out in the perso blob buffer as follows:
   * - 16 bit object header
   * - 16 bits cert wrapper header
   * - Certificate name string
   * - Cerificate data itself
   *
   * Note that both certificate and object headers'
   * are 16 bit integers in big endian format.
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
   */
  perso_tlv_object_header_t obj_header = 0;
  perso_tlv_cert_header_t cert_header = 0;
  size_t name_len;
  size_t obj_len;
  size_t wrapped_len;

  // strlen() is not available.
  name_len = 0;
  while (name[name_len])
    name_len++;

  if (name_len > kCrthNameSizeFieldMask)
    return OUT_OF_RANGE();

  wrapped_len = sizeof(perso_tlv_cert_header_t) + name_len + cert_size;
  obj_len = wrapped_len + sizeof(perso_tlv_object_header_t);

  if (obj_len > (sizeof(pb->body) - pb->next_free))
    return OUT_OF_RANGE();

  if (needs_endorsement) {
    PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Tbs);
  } else {
    PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Cert);
  }

  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, obj_len);

  PERSO_TLV_SET_FIELD(Crth, Size, cert_header, wrapped_len);
  PERSO_TLV_SET_FIELD(Crth, NameSize, cert_header, name_len);

  TRY(perso_tlv_push_to_blob(&obj_header, sizeof(obj_header), pb));
  TRY(perso_tlv_push_to_blob(&cert_header, sizeof(cert_header), pb));
  TRY(perso_tlv_push_to_blob(name, name_len, pb));
  TRY(perso_tlv_push_to_blob(cert_body, cert_size, pb));
  pb->num_objs++;
  LOG_INFO("Generated %s certificate.", name);

  return OK_STATUS();
}
