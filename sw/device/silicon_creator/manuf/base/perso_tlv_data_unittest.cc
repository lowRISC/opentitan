// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include <array>
#include <cstring>
#include <gtest/gtest.h>
#include <string>

#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/error.h"

const uint8_t kX509CertTestdata[132] = {0x30, 0x82, 0x00, 0x80};
const size_t kX509CertTestdataSize = 132;

namespace perso_tlv_data_unittest {
namespace {

class PersoTlvDataTest : public testing::Test {
 public:
  // A small scratch buffer used for tests.
  static constexpr size_t kScratchBufferSize = 256;
  std::array<uint8_t, kScratchBufferSize> scratch_buf_;

  void SetUp() override { scratch_buf_.fill(0); }

  void TearDown() override { scratch_buf_.fill(0); }
};

TEST_F(PersoTlvDataTest, PersoTlvCertObjBuildX509Cert) {
  const char *name = "UDS";
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = kScratchBufferSize;

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV0, scratch_buf_.data(),
                                     &buf_size),
            kErrorOk);

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = buf_size;  // Simulate reading the built object back

  // Should be able to get the object from the built buffer
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorOk);

  EXPECT_EQ(obj.obj_type, (uint32_t)obj_type);
  EXPECT_EQ(obj.obj_size, buf_size);  // The reported size by build should match
                                      // the object's size field
  EXPECT_STREQ(obj.name, name);
  EXPECT_EQ(obj.cert_body_size, cert_size);
  EXPECT_EQ(memcmp(obj.cert_body_p, cert, cert_size), 0);
}

TEST_F(PersoTlvDataTest, PersoTlvCertObjBuildBufTooSmall) {
  const char *name = "UDS";
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = 10;  // Intentionally too small

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV0, scratch_buf_.data(),
                                     &buf_size),
            kErrorPersoTlvOutputBufTooSmall);
}

TEST_F(PersoTlvDataTest, PersoTlvCertObjBuildNameTooLong) {
  // Name length field is 4 bits, so max length is 15.
  const char *name = "ThisNameIsTooLongFor4Bits";  // Length > 15
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = kScratchBufferSize;

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV0, scratch_buf_.data(),
                                     &buf_size),
            kErrorPersoTlvCertNameTooLong);
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjEmptyBuf) {
  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = 0;
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);  // Not enough size for header
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjBufTooSmallForHeader) {
  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = sizeof(perso_tlv_object_header_t) - 1;
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjEmptyObject) {
  // Create a minimal object header with size 0
  perso_tlv_object_header_t obj_header = 0;
  PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Cert);
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, 0);  // Size 0

  memcpy(scratch_buf_.data(), &obj_header, sizeof(obj_header));

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = sizeof(obj_header);
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvCertObjNotFound);  // Object is empty
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjTooBigForBuf) {
  // Create an object header that claims to be larger than the buffer
  perso_tlv_object_header_t obj_header = 0;
  PERSO_TLV_SET_FIELD(Objh, Type, obj_header, kPersoObjectTypeX509Cert);
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header,
                      (uint16_t)(kScratchBufferSize + 1));  // Size too large

  memcpy(scratch_buf_.data(), &obj_header, sizeof(obj_header));

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = sizeof(obj_header);  // Only header is actually in buf
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);  // Object exceeds buffer size
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjBufTooSmallForCertHeader) {
  // Create a minimal object header for a cert
  perso_tlv_object_header_t obj_header = 0;
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  size_t tlv_buf_size = sizeof(obj_header) + 1;
  PERSO_TLV_SET_FIELD(Objh, Type, obj_header, obj_type);
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, (uint16_t)tlv_buf_size);

  memcpy(scratch_buf_.data(), &obj_header, sizeof(obj_header));

  perso_tlv_cert_obj_t obj;
  // Provide buffer size just enough for object header
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);  // Not enough size for cert header
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjSizeMismatch) {
  // Create headers where the tlv cert size doesn't match x509 cert size
  perso_tlv_object_header_t obj_header = 0;
  perso_tlv_cert_header_t cert_header = 0;
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  std::string name_str = "UDS";
  size_t cert_data_size = kX509CertTestdataSize;
  size_t expected_total_size = sizeof(obj_header) + sizeof(cert_header) +
                               name_str.size() + cert_data_size;

  PERSO_TLV_SET_FIELD(Objh, Type, obj_header, obj_type);
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, (uint16_t)expected_total_size);
  PERSO_TLV_SET_FIELD(Crth, NameSize, cert_header, (uint16_t)name_str.size());
  // Set cert header size *incorrectly*
  PERSO_TLV_SET_FIELD(Crth, Size, cert_header,
                      (uint16_t)(expected_total_size - sizeof(obj_header) - 1));

  uint8_t *ptr = scratch_buf_.data();
  memcpy(ptr, &obj_header, sizeof(obj_header));
  ptr += sizeof(obj_header);
  memcpy(ptr, &cert_header, sizeof(cert_header));
  ptr += sizeof(cert_header);
  memcpy(ptr, name_str.data(), name_str.size());
  ptr += name_str.size();
  memcpy(ptr, kX509CertTestdata, cert_data_size);

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size =
      expected_total_size;  // Buffer is large enough for actual data
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);  // Size mismatch detected by sanity check
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjCertTooLong) {
  // Create a TLV object with partial cert.
  perso_tlv_object_header_t obj_header = 0;
  perso_tlv_cert_header_t cert_header = 0;
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const size_t name_len = 7;  // Arbitrary name length
  // Total object size should account for headers and the name, but we will
  // provide a smaller buffer size to simulate the error condition.
  size_t cert_obj_size = sizeof(cert_header) + name_len + kX509CertTestdataSize;
  // Provide buffer size enough for headers, but NOT the full cert body
  size_t tlv_buf_size = sizeof(obj_header) + cert_obj_size - 1;

  PERSO_TLV_SET_FIELD(Objh, Type, obj_header, obj_type);
  PERSO_TLV_SET_FIELD(Objh, Size, obj_header, (uint16_t)tlv_buf_size);
  PERSO_TLV_SET_FIELD(Crth, NameSize, cert_header, (uint16_t)name_len);
  PERSO_TLV_SET_FIELD(Crth, Size, cert_header, (uint16_t)cert_obj_size);

  memcpy(scratch_buf_.data(), &obj_header, sizeof(obj_header));
  memcpy(scratch_buf_.data() + sizeof(obj_header), &cert_header,
         sizeof(cert_header));

  perso_tlv_cert_obj_t obj;
  // Expected to fail due to wrapped_cert_size is too long.
  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvInternal);
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjX509SanityCheckPass) {
  // Build a valid X.509 cert object first
  const char *name = "UDS";
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = kScratchBufferSize;

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV0, scratch_buf_.data(),
                                     &buf_size),
            kErrorOk);

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = buf_size;

  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorOk);
}

TEST_F(PersoTlvDataTest, PersoTlvGetCertObjInvalidObjType) {
  // Build a X.509 cert object with invalid kPersoObjectTypeDeviceId type.
  const char *name = "UDS";
  perso_tlv_object_type_t obj_type = kPersoObjectTypeDeviceId;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = kScratchBufferSize;

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV0, scratch_buf_.data(),
                                     &buf_size),
            kErrorOk);

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = buf_size;

  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV0, &obj),
            kErrorPersoTlvCertObjNotFound);
}

TEST_F(PersoTlvDataTest, PersoTlvCertObjBuildX509CertV1) {
  const char *name = "MLDSA-CERT";
  perso_tlv_object_type_t obj_type = kPersoObjectTypeX509Cert;
  const uint8_t *cert = kX509CertTestdata;
  size_t cert_size = kX509CertTestdataSize;
  size_t buf_size = kScratchBufferSize;

  EXPECT_EQ(perso_tlv_cert_obj_build(name, obj_type, cert, cert_size,
                                     kPersoBlobVersionV1, scratch_buf_.data(),
                                     &buf_size),
            kErrorOk);

  perso_tlv_cert_obj_t obj;
  size_t tlv_buf_size = buf_size;

  EXPECT_EQ(perso_tlv_get_cert_obj(scratch_buf_.data(), tlv_buf_size,
                                   kPersoBlobVersionV1, &obj),
            kErrorOk);

  EXPECT_EQ(obj.obj_type, (uint32_t)obj_type);
  EXPECT_EQ(obj.obj_size, buf_size);
  EXPECT_STREQ(obj.name, name);
  EXPECT_EQ(obj.cert_body_size, cert_size);
  EXPECT_EQ(memcmp(obj.cert_body_p, cert, cert_size), 0);
}

TEST_F(PersoTlvDataTest, PersoTlvInitV1Blob) {
  perso_blob_t pb = {0};
  EXPECT_EQ(perso_tlv_init_v1_blob(&pb), kErrorOk);
  EXPECT_EQ(pb.num_objs, (size_t)1);
  EXPECT_EQ(pb.next_free, (size_t)(sizeof(perso_tlv_object_header_t) +
                                   sizeof(perso_tlv_blob_version_payload_t)));

  perso_blob_version_t version;
  size_t offset;
  EXPECT_EQ(
      perso_tlv_get_blob_version(pb.body, pb.next_free, &version, &offset),
      kErrorOk);
  EXPECT_EQ(version, kPersoBlobVersionV1);
  EXPECT_EQ(offset, pb.next_free);
}

TEST_F(PersoTlvDataTest, PersoTlvPushObjectToPersoBlobV1) {
  perso_blob_t pb = {0};
  EXPECT_EQ(perso_tlv_init_v1_blob(&pb), kErrorOk);

  uint32_t data[] = {0x11223344, 0x55667788};
  EXPECT_EQ(perso_tlv_push_object_to_perso_blob(kPersoObjectTypeDeviceId, data,
                                                sizeof(data),
                                                kPersoBlobVersionV1, &pb),
            kErrorOk);

  EXPECT_EQ(pb.num_objs, (size_t)2);
  EXPECT_EQ((uint32_t)perso_tlv_object_type(pb.body + 4, kPersoBlobVersionV1),
            (uint32_t)kPersoObjectTypeDeviceId);
  EXPECT_EQ(perso_tlv_object_size(pb.body + 4, kPersoBlobVersionV1),
            (uint32_t)(sizeof(perso_tlv_object_header_v1_t) + sizeof(data)));
}

}  // namespace
}  // namespace perso_tlv_data_unittest
