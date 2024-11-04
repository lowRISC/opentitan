// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/error.h"

rom_error_t perso_tlv_get_cert_obj(uint8_t *buf, size_t ltv_buf_size,
                                   perso_tlv_cert_obj_t *obj) {
  perso_tlv_object_header_t objh;
  perso_tlv_object_type_t obj_type;
  uint16_t obj_size;

  // Extract LTV object header, including: size and type.
  obj->obj_p = buf;
  memcpy(&objh, buf, sizeof(perso_tlv_object_header_t));
  // Extract LTV object size.
  PERSO_TLV_GET_FIELD(Objh, Size, objh, &obj_size);
  if (obj_size == 0)
    return kErrorPersoTlvCertObjNotFound;  // Object is empty.
  if (obj_size > ltv_buf_size)
    return kErrorPersoTlvInternal;  // Object exceeds the size of host buffer.
  obj->obj_size = obj_size;
  // Extract LTV object type.
  PERSO_TLV_GET_FIELD(Objh, Type, objh, &obj_type);
  if (obj_type != kPersoObjectTypeX509Cert) {
    LOG_INFO("Skipping object of type %d", obj_type);
    return kErrorPersoTlvCertObjNotFound;
  }
  buf += sizeof(perso_tlv_object_header_t);
  ltv_buf_size -= sizeof(perso_tlv_object_header_t);

  // If we made it this far, we found a certificate LTV object, so we will parse
  // the object's header and metadata next.

  perso_tlv_cert_header_t crth;
  uint16_t wrapped_cert_size;
  uint16_t name_len;

  // Extract the certificate object header, including: certificate object and
  // nameksizes, certificate name string, and pointer to the certificate body.
  memcpy(&crth, buf, sizeof(perso_tlv_cert_header_t));
  // Extract certificate name size.
  PERSO_TLV_GET_FIELD(Crth, NameSize, crth, &name_len);
  // Extract wrapped certificate object size.
  PERSO_TLV_GET_FIELD(Crth, Size, crth, &wrapped_cert_size);
  // There are at least 4 bytes in an X.509 ASN.1 DER certificate: two bytes of
  // header and two bytes of size data.
  if ((wrapped_cert_size < (sizeof(perso_tlv_cert_header_t) + name_len + 4)) ||
      (wrapped_cert_size > ltv_buf_size))
    return kErrorPersoTlvInternal;  // Something is really screwed up.
  buf += sizeof(perso_tlv_cert_header_t);
  ltv_buf_size -= sizeof(perso_tlv_cert_header_t);
  // Extract certificate name string.
  memcpy(obj->name, buf, name_len);
  obj->name[name_len] = '\0';
  buf += name_len;
  ltv_buf_size -= name_len;
  // Set pointer to certificate body.
  obj->cert_body_size =
      wrapped_cert_size - sizeof(perso_tlv_cert_header_t) - name_len;
  obj->cert_body_p = buf;

  // Sanity check on the certificate body size.
  size_t decoded_cert_size =
      cert_x509_asn1_decode_size_header(obj->cert_body_p);
  if (decoded_cert_size != obj->cert_body_size) {
    LOG_ERROR("Unexpected cert size %d instead of %d for cert %s",
              decoded_cert_size, obj->cert_body_size, obj->name);
    return kErrorPersoTlvInternal;
  }

  return kErrorOk;
}

rom_error_t perso_tlv_cert_obj_build(const char *name, bool needs_endorsement,
                                     const uint8_t *cert, size_t cert_size,
                                     uint8_t *buf, size_t *buf_size) {
  perso_tlv_object_header_t obj_header = 0;
  perso_tlv_cert_header_t cert_header = 0;
  size_t obj_size;
  size_t wrapped_cert_size;

  // Compute the name length (strlen() is not available).
  size_t name_len = 0;
  while (name[name_len])
    name_len++;
  if (name_len > kCrthNameSizeFieldMask)
    return kErrorPersoTlvCertNameTooLong;

  // Compute the wrapped certificate object (cert header + cert data) and perso
  // LTV object sizes.
  wrapped_cert_size = sizeof(perso_tlv_cert_header_t) + name_len + cert_size;
  obj_size = wrapped_cert_size + sizeof(perso_tlv_object_header_t);

  // Check there is enough room in the buffer to store the perso LTV object.
  if (obj_size > *buf_size)
    return kErrorPersoTlvOutputBufTooSmall;

  // Setup the perso LTV object header.
  if (needs_endorsement) {
    PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Tbs);
  } else {
    PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Cert);
  }
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, obj_size);

  // Setup the cert object header.
  PERSO_TLV_SET_FIELD(Crth, Size, cert_header, wrapped_cert_size);
  PERSO_TLV_SET_FIELD(Crth, NameSize, cert_header, name_len);

  // Push the cert perso LTV object to the buffer.
  // Return the size of the buffer that was used up by this perso LTV object.
  *buf_size = 0;
  memcpy(buf + *buf_size, &obj_header, sizeof(perso_tlv_object_header_t));
  *buf_size += sizeof(perso_tlv_object_header_t);
  memcpy(buf + *buf_size, &cert_header, sizeof(perso_tlv_cert_header_t));
  *buf_size += sizeof(perso_tlv_cert_header_t);
  memcpy(buf + *buf_size, name, name_len);
  *buf_size += name_len;
  memcpy(buf + *buf_size, cert, cert_size);
  *buf_size += cert_size;

  return kErrorOk;
}

status_t perso_tlv_push_cert_to_perso_blob(const char *name,
                                           bool needs_endorsement,
                                           const uint8_t *cert,
                                           size_t cert_size, perso_blob_t *pb) {
  // Build the perso TLV cert object and push it to the perso blob.
  size_t obj_size = sizeof(pb->body) - pb->next_free;
  TRY(perso_tlv_cert_obj_build(name, needs_endorsement, cert, cert_size,
                               pb->body + pb->next_free, &obj_size));

  // Update the perso blob offset and object count.
  pb->next_free += obj_size;
  pb->num_objs++;

  return OK_STATUS();
}

status_t perso_tlv_push_to_perso_blob(const void *data, size_t size,
                                      perso_blob_t *perso_blob) {
  size_t room = sizeof(perso_blob->body) - perso_blob->next_free;
  if (room < size)
    return RESOURCE_EXHAUSTED();
  memcpy(perso_blob->body + perso_blob->next_free, data, size);
  perso_blob->next_free += size;
  return OK_STATUS();
}
