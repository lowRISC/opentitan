// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/asn1.h"

#include <array>
#include <cstring>

#include "gtest/gtest.h"

/**
 * Make sure that an array has the right size and matches
 *
 * the content of another constant array.
 * @param array Pointer to an array.
 * @param size Size in bytes of the array.
 * @param const_expected_result Pointer to an expected result: sizeof() must
 * return the correct size.
 */
#define EXPECT_EQ_CONST_ARRAY(array, size, const_expected_result) \
  do {                                                            \
    EXPECT_EQ(size, sizeof(const_expected_result));               \
    EXPECT_EQ(0, memcmp(array, const_expected_result,             \
                        sizeof(const_expected_result)));          \
  } while (0)

namespace asn1_unittest {
namespace {

// Make sure that we can start and finish with an empty buffer.
TEST(Asn1, CreateFinish) {
  asn1_state_t state;
  uint8_t buf[1] = {0xff};
  // Pretend that buffer has size 0 for testing.
  EXPECT_EQ(asn1_start(&state, buf, 0), kErrorOk);
  size_t out_size = 42;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  EXPECT_EQ(out_size, 0);
  EXPECT_EQ(buf[0], 0xff);
}

// Make sure that we can push a byte and that we cannot overflow.
TEST(Asn1, PushByte) {
  asn1_state_t state;
  uint8_t buf[1] = {0xff};
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_byte(&state, 0xa5), kErrorOk);
  // Buffer is full, expect an error.
  EXPECT_EQ(asn1_push_byte(&state, 0xb6), kErrorAsn1BufferExhausted);
  size_t out_size = 42;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  EXPECT_EQ(out_size, 1);
  EXPECT_EQ(buf[0], 0xa5);
}

// Make sure that we can push multiple bytes.
TEST(Asn1, PushBytes) {
  asn1_state_t state;
  uint8_t buf[3] = {0xff, 0xff, 0xff};
  const uint8_t kData[] = {0xa5, 0xb6};
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_bytes(&state, kData, sizeof(kData)), kErrorOk);
  size_t out_size = 42;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kData);
  EXPECT_EQ(buf[2], 0xff);
}

// Make sure that we can push multiple bytes.
TEST(Asn1, PushBytesOverflow) {
  asn1_state_t state;
  uint8_t buf[3] = {0xff, 0xff, 0xff};
  const uint8_t kData[] = {0xa5, 0xb6, 0x32, 0xff};
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_bytes(&state, kData, sizeof(kData)),
            kErrorAsn1BufferExhausted);
}

// Make sure that we can push an empty tag.
TEST(Asn1, PushEmptyTag) {
  asn1_state_t state;
  uint8_t buf[16];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_tag_t tag;
  EXPECT_EQ(asn1_start_tag(&state, &tag, kAsn1TagNumberSequence), kErrorOk);
  EXPECT_EQ(asn1_finish_tag(&tag), kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      0x30, 0x00,  // Identifier octet, length, no contents.
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push a boolean.
TEST(Asn1, PushBoolean) {
  asn1_state_t state;
  uint8_t buf[16];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_bool(&state, true), kErrorOk);
  EXPECT_EQ(asn1_push_bool(&state, false), kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, boolean), length, content (can be any
      // nonzero value, the library uses 0xff).
      0x01, 0x01, 0xff, 0x01, 0x01, 0x00,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push small integers.
TEST(Asn1, PushInt32) {
  asn1_state_t state;
  uint8_t buf[24];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_uint32(&state, kAsn1TagNumberInteger, 0), kErrorOk);
  EXPECT_EQ(asn1_push_int32(&state, kAsn1TagNumberInteger, 0x1234), kErrorOk);
  EXPECT_EQ(asn1_push_uint32(&state, kAsn1TagNumberOctetString, 0x8000),
            kErrorOk);
  EXPECT_EQ(asn1_push_int32(&state, kAsn1TagNumberInteger, -1), kErrorOk);
  EXPECT_EQ(asn1_push_int32(&state, kAsn1TagNumberInteger, -3000), kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, integer), length, content (minimal
      // encoding, always uses one byte at least).
      0x02, 0x01, 0x0, 0x02, 0x02, 0x12, 0x34,
      // Identifier octet (universal, octet string), length, content (minimal
      // encoding, needs 0x00 because MSB is set).
      0x04, 0x03, 0x00, 0x80, 0x00,
      // Identifier octet (universal, integer), length, content (minimal
      // encoding for signed integers).
      0x02, 0x01, 0xff, 0x02, 0x02, 0xf4, 0x48};
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push big integers.
TEST(Asn1, PushIntUnsigned) {
  asn1_state_t state;
  uint8_t buf[16];
  // Integers are in big-endian.
  const uint8_t kBigInt1[] = {0x00, 0x00, 0x00, 0x00,
                              0x00};              // Extra zeroes for testing.
  const uint8_t kBigInt2[] = {0x00, 0x12, 0x34};  // Extra zeroes for testing.
  const uint8_t kBigInt3[] = {0x00, 0x00, 0x00, 0x80,
                              0x00};  // Extra zeroes for testing.
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt1,
                              sizeof(kBigInt1)),
            kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt2,
                              sizeof(kBigInt2)),
            kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt3,
                              sizeof(kBigInt3)),
            kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, integer), length, content (minimal
      // encoding, always uses one byte at least).
      0x02, 0x01, 0x0,  0x02, 0x02, 0x12,
      0x34, 0x02, 0x03, 0x00, 0x80, 0x00,  // Needs 0x00 because MSB is set.
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push big integers.
TEST(Asn1, PushIntSigned) {
  asn1_state_t state;
  uint8_t buf[12];
  // Integers are in big-endian.
  const uint8_t kBigInt1[] = {0x00, 0x00, 0x00, 0x00,
                              0x00};              // Extra zeroes for testing.
  const uint8_t kBigInt2[] = {0xff, 0xff, 0xff};  // Extra ones for testing.
  const uint8_t kBigInt3[] = {0xff, 0xff, 0xf4,
                              0x48};  // Extra zeroes for testing.
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt1,
                              sizeof(kBigInt1)),
            kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt2,
                              sizeof(kBigInt2)),
            kErrorOk);
  EXPECT_EQ(asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt3,
                              sizeof(kBigInt3)),
            kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, integer), length, content (minimal
      // encoding, always uses one byte at least).
      0x02, 0x01, 0x0, 0x02, 0x01, 0xff, 0x02, 0x02, 0xf4, 0x48,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push strings.
TEST(Asn1, PushStrings) {
  asn1_state_t state;
  uint8_t buf[30];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  const char kString1[] = "lowRISC";
  const char kString2[] = "OpenTitanAndMore!";
  const char kString3[] = "";
  EXPECT_EQ(asn1_push_string(&state, kAsn1TagNumberPrintableString, kString1,
                             strlen(kString1)),
            kErrorOk);
  // Cut the second string short on purpose.
  EXPECT_EQ(asn1_push_string(&state, kAsn1TagNumberUtf8String, kString2, 9),
            kErrorOk);
  EXPECT_EQ(asn1_push_string(&state, kAsn1TagNumberOctetString, kString3,
                             strlen(kString3)),
            kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  // clang-format off
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, printable string), length, content.
      0x13, 0x07, 0x6c, 0x6f, 0x77, 0x52, 0x49, 0x53, 0x43,
      // Identifier octet (universal, integer), length, content.
      0x0c, 0x09, 0x4f, 0x70, 0x65, 0x6e, 0x54, 0x69, 0x74, 0x61, 0x6e,
      // Identifier octet (universal, integer), length, no content.
      0x04, 0x00,
  };
  // clang-format on
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push strings.
TEST(Asn1, PushRawOid) {
  asn1_state_t state;
  uint8_t buf[30];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  const uint8_t kRawOid[] = {0x88, 0x037, 0x03};  // Corresponds to "2.999.3".
  EXPECT_EQ(asn1_push_oid_raw(&state, kRawOid, sizeof(kRawOid)), kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, OID), length, content (encoded as per
      // X.690 section 8.19.5).
      0x06, 0x03, 0x88, 0x037, 0x03,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push strings.
TEST(Asn1, PushHexStrings) {
  asn1_state_t state;
  uint8_t buf[12];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  const uint8_t kData[] = {0x01, 0x23, 0xab, 0xef};
  EXPECT_EQ(asn1_push_hexstring(&state, kAsn1TagNumberPrintableString, kData,
                                sizeof(kData)),
            kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const uint8_t kExpectedResult[] = {
      // Identifier octet (universal, printable string), length, content.
      0x13, 0x08, 0x30, 0x31, 0x32, 0x33, 0x61, 0x62, 0x65, 0x66,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that the tag encoding is correct.
TEST(Asn1, TagLengthEncoding) {
  asn1_state_t state;
  std::vector<uint8_t> buf;
  buf.resize(0xfffff);
  std::vector<uint8_t> expected;

#define ADD_BYTES(fill, fill_size, ...)                                        \
  do {                                                                         \
    std::vector<uint8_t> tmp(fill_size, fill);                                 \
    const uint8_t kData[] = {__VA_ARGS__};                                     \
    expected.push_back(0x30); /* Identifier octet (universal, sequence). */    \
    expected.insert(expected.end(), kData,                                     \
                    kData + sizeof(kData)); /* Length encoding */              \
    expected.insert(expected.end(), tmp.begin(), tmp.end());                   \
    asn1_tag_t tag;                                                            \
    EXPECT_EQ(asn1_start_tag(&state, &tag, kAsn1TagNumberSequence), kErrorOk); \
    EXPECT_EQ(asn1_push_bytes(&state, &tmp[0], tmp.size()), kErrorOk);         \
    EXPECT_EQ(asn1_finish_tag(&tag), kErrorOk);                                \
  } while (0)

  EXPECT_EQ(asn1_start(&state, &buf[0], buf.size()), kErrorOk);
  ADD_BYTES(0x00, 0, 0x00);
  ADD_BYTES(0xa5, 0x7f, 0x7f);
  ADD_BYTES(0xb6, 0x80, 0x81, 0x80);
  ADD_BYTES(0xc7, 0xff, 0x81, 0xff);
  ADD_BYTES(0xd8, 0x100, 0x82, 0x01, 0x00);
  ADD_BYTES(0xe9, 0xffff, 0x82, 0xff, 0xff);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  EXPECT_EQ(out_size, expected.size());
  buf.resize(out_size);
  EXPECT_EQ(buf, expected);
}

}  // namespace
}  // namespace asn1_unittest
