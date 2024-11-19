// Copyright lowRISC contributors (OpenTitan project).
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
 * @param expected_result An std::array or vector containing the expected
 * result.
 */
#define EXPECT_EQ_CONST_ARRAY(array, array_size, expected_result)              \
  do {                                                                         \
    EXPECT_EQ(array_size, expected_result.size());                             \
    EXPECT_EQ(true, std::equal(expected_result.begin(), expected_result.end(), \
                               array));                                        \
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
  asn1_push_byte(&state, 0xa5);
  EXPECT_EQ(state.error, kErrorOk);

  // Buffer is full, expect an error.
  asn1_push_byte(&state, 0xb6);
  EXPECT_EQ(state.error, kErrorAsn1BufferExhausted);
  asn1_clear_error(&state);

  size_t out_size = 42;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  EXPECT_EQ(out_size, 1);
  EXPECT_EQ(buf[0], 0xa5);
}

// Make sure that we can push multiple bytes.
TEST(Asn1, PushBytes) {
  asn1_state_t state;
  uint8_t buf[3] = {0xff, 0xff, 0xff};
  const std::array<uint8_t, 2> kData = {0xa5, 0xb6};
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_push_bytes(&state, kData.begin(), kData.size());
  EXPECT_EQ(state.error, kErrorOk);
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
  asn1_push_bytes(&state, kData, sizeof(kData));
  EXPECT_EQ(state.error, kErrorAsn1BufferExhausted);
  asn1_clear_error(&state);
}

// Make sure that we can push an empty tag.
TEST(Asn1, PushEmptyTag) {
  asn1_state_t state;
  uint8_t buf[16];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_tag_t tag;
  asn1_start_tag(&state, &tag, kAsn1TagNumberSequence);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 2> kExpectedResult = {
      0x30, 0x00,  // Identifier octet, length, no contents.
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push a boolean.
TEST(Asn1, PushBoolean) {
  asn1_state_t state;
  uint8_t buf[16];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_push_bool(&state, kAsn1TagNumberBoolean, true);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_bool(&state, kAsn1TagClassContext | 42, false);
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 6> kExpectedResult = {
      // Identifier octet (universal, boolean), length, content (can be any
      // nonzero value, the library uses 0xff).
      0x01, 0x01, 0xff, 0xaa, 0x01, 0x00,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push small integers.
TEST(Asn1, PushInt32) {
  asn1_state_t state;
  uint8_t buf[24];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_push_uint32(&state, kAsn1TagNumberInteger, 0);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_int32(&state, kAsn1TagNumberInteger, 0x1234);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_uint32(&state, kAsn1TagNumberOctetString, 0x8000);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_int32(&state, kAsn1TagNumberInteger, -1);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_int32(&state, kAsn1TagNumberInteger, -3000);
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 19> kExpectedResult = {
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
  asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt1,
                    sizeof(kBigInt1));
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt2,
                    sizeof(kBigInt2));
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer(&state, kAsn1TagNumberInteger, false, kBigInt3,
                    sizeof(kBigInt3));
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 12> kExpectedResult = {
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
  asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt1,
                    sizeof(kBigInt1));
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt2,
                    sizeof(kBigInt2));
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer(&state, kAsn1TagNumberInteger, true, kBigInt3,
                    sizeof(kBigInt3));
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 10> kExpectedResult = {
      // Identifier octet (universal, integer), length, content (minimal
      // encoding, always uses one byte at least).
      0x02, 0x01, 0x0, 0x02, 0x01, 0xff, 0x02, 0x02, 0xf4, 0x48,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push big integers with padding.
TEST(Asn1, PushIntPad) {
  asn1_state_t state;
  uint8_t buf[40];
  // Integers are in big-endian.
  const uint8_t kBigInt1[] = {0x42};
  const uint8_t kBigInt2[] = {0x00, 0x80};  // Extra zeroes for testing.
  const uint8_t kBigInt3[] = {0x80, 0x01};
  const uint8_t kBigInt4[] = {0x30, 0x47, 0x80, 0x01};
  const uint8_t kBigInt5[] = {0x30, 0x47, 0x80, 0x01, 0x17};
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_push_integer_pad(&state, false, kBigInt1, sizeof(kBigInt1), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, true, kBigInt1, sizeof(kBigInt1), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, false, kBigInt2, sizeof(kBigInt2), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, true, kBigInt2, sizeof(kBigInt2), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, false, kBigInt3, sizeof(kBigInt3), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, true, kBigInt3, sizeof(kBigInt3), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, false, kBigInt4, sizeof(kBigInt4), 4);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_integer_pad(&state, true, kBigInt4, sizeof(kBigInt4), 4);
  EXPECT_EQ(state.error, kErrorOk);

  asn1_push_integer_pad(&state, true, kBigInt5, sizeof(kBigInt5), 4);
  EXPECT_EQ(state.error, kErrorAsn1PushIntegerPadInvalidArgument);
  asn1_clear_error(&state);

  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 32> kExpectedResult = {
      // Unsigned: padded with 0.
      0x00, 0x00, 0x00, 0x42,
      // Signed and non-negative: padded with 0.
      0x00, 0x00, 0x00, 0x42,
      // Unsigned: padded with 0.
      0x00, 0x00, 0x00, 0x80,
      // Signed and non-negative: padded with 0.
      0x00, 0x00, 0x00, 0x80,
      // Unsigned: padded with 0.
      0x00, 0x00, 0x80, 0x01,
      // Signed and negative: padded with 0xff.
      0xff, 0xff, 0x80, 0x01,
      // Already at maximum size: no padding.
      0x30, 0x47, 0x80, 0x01,
      // Already at maximum size: no padding.
      0x30, 0x47, 0x80, 0x01};
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
  asn1_push_string(&state, kAsn1TagNumberPrintableString, kString1,
                   strlen(kString1));
  EXPECT_EQ(state.error, kErrorOk);
  // Cut the second string short on purpose.
  asn1_push_string(&state, kAsn1TagNumberUtf8String, kString2, 9);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_push_string(&state, kAsn1TagNumberOctetString, kString3,
                   strlen(kString3));
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  // clang-format off
  const std::array<uint8_t, 22> kExpectedResult = {
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

// Make sure that we can push bitstrings.
TEST(Asn1, PushBitString) {
  asn1_state_t state;
  uint8_t buf[20];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  asn1_bitstring_t bitstring;
  asn1_tag_t tag;
  // Empty bitstring.
  asn1_start_tag(&state, &tag, kAsn1TagNumberBitString);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_start_bitstring(&state, &bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_bitstring(&bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorOk);
  // Two trivial bitstrings.
  asn1_start_tag(&state, &tag, kAsn1TagNumberBitString);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_start_bitstring(&state, &bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_bitstring_push_bit(&bitstring, true);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_bitstring(&bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorOk);

  asn1_start_tag(&state, &tag, kAsn1TagNumberBitString);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_start_bitstring(&state, &bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_bitstring_push_bit(&bitstring, false);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_bitstring(&bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorOk);
  // A longer bitstring.
  const std::array<bool, 12> kBitString = {
      true,  false, true, true,  false, false,
      false, false, true, false, false, true,
  };
  asn1_start_tag(&state, &tag, kAsn1TagNumberBitString);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_start_bitstring(&state, &bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  for (bool bit : kBitString) {
    asn1_bitstring_push_bit(&bitstring, bit);
    EXPECT_EQ(state.error, kErrorOk);
  }
  asn1_finish_bitstring(&bitstring);
  EXPECT_EQ(state.error, kErrorOk);
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 16> kExpectedResult = {
      // Identifier octet (bitstring, OID), length, content (encoded as per
      // X.690 section 8.6).
      0x03, 0x01, 0x0,
      // Identifier octet (bitstring, OID), length, content.
      0x03, 0x02, 0x7, 0x80,
      // Identifier octet (bitstring, OID), length, content.
      0x03, 0x02, 0x7, 0x00,
      // Identifier octet (bitstring, OID), length, content (written in binary
      // to make it easier to read).
      0x03, 0x03, 0x04, 0b10110000, 0b10010000};
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that we can push strings.
TEST(Asn1, PushRawOid) {
  asn1_state_t state;
  uint8_t buf[30];
  EXPECT_EQ(asn1_start(&state, buf, sizeof(buf)), kErrorOk);
  const uint8_t kRawOid[] = {0x88, 0x037, 0x03};  // Corresponds to "2.999.3".
  asn1_push_oid_raw(&state, kRawOid, sizeof(kRawOid));
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 5> kExpectedResult = {
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
  asn1_push_hexstring(&state, kAsn1TagNumberPrintableString, kData,
                      sizeof(kData));
  EXPECT_EQ(state.error, kErrorOk);
  size_t out_size;
  EXPECT_EQ(asn1_finish(&state, &out_size), kErrorOk);
  const std::array<uint8_t, 10> kExpectedResult = {
      // Identifier octet (universal, printable string), length, content.
      0x13, 0x08, 0x30, 0x31, 0x32, 0x33, 0x61, 0x62, 0x65, 0x66,
  };
  EXPECT_EQ_CONST_ARRAY(buf, out_size, kExpectedResult);
}

// Make sure that the tag routines handle overflow correctly.
TEST(Asn1, TagOverflow) {
  // When creating a tag, `asn1_start_tag` initially assumes that
  // the length encoding fits on one byte, and this is fixed-up
  // in `asn1_finish_tag` by moving the data. There is a potential
  // source of overflow here if (one byte length) + (data) fits into
  // the buffer but (two byte length) + (data) which is the correct
  // final value does not. In this test, we create create a buffer that
  // is big enough to hold the final value but we pretend that it is one
  // byte smaller. If the code is correct, it should return an error
  // saying that the buffer is too small. If it is incorrect, it will
  // (incorrect) proceed and write one byte after the end of the buffer.
  asn1_state_t state;
  std::vector<uint8_t> buf;
  const uint8_t kPattern = 0xa5;
  // Allocate one byte for the tag, one for the length, 0x100 for the data.
  const size_t kBufferSize = 1 + 1 + 0x100;
  buf.resize(kBufferSize + 1, kPattern);
  EXPECT_EQ(asn1_start(&state, &buf[0], kBufferSize), kErrorOk);
  // The function will allocate one byte for the tag length.
  asn1_tag_t tag;
  asn1_start_tag(&state, &tag, kAsn1TagNumberSequence);
  EXPECT_EQ(state.error, kErrorOk);
  // Push 0x100 bytes so that the length tag requires two bytes.
  std::vector<uint8_t> tmp;
  tmp.resize(0x100, 0xff);
  asn1_push_bytes(&state, &tmp[0], tmp.size());
  EXPECT_EQ(state.error, kErrorOk);
  // At this point, the function will need to move the data forward by one byte
  // so it should hit the buffer size.
  asn1_finish_tag(&tag);
  EXPECT_EQ(state.error, kErrorAsn1BufferExhausted);
  asn1_clear_error(&state);
  // Make sure that that even though it returned an error, the function did not
  // actually write anything past the end of the buffer.
  EXPECT_EQ(buf[kBufferSize], kPattern);
}

// Make sure that the tag encoding is correct.
TEST(Asn1, TagLengthEncoding) {
  asn1_state_t state;
  std::vector<uint8_t> buf;
  buf.resize(0xfffff);
  std::vector<uint8_t> expected;

#define ADD_BYTES(fill, fill_size, ...)                                     \
  do {                                                                      \
    std::vector<uint8_t> tmp(fill_size, fill);                              \
    const uint8_t kData[] = {__VA_ARGS__};                                  \
    expected.push_back(0x30); /* Identifier octet (universal, sequence). */ \
    expected.insert(expected.end(), kData,                                  \
                    kData + sizeof(kData)); /* Length encoding */           \
    expected.insert(expected.end(), tmp.begin(), tmp.end());                \
    asn1_tag_t tag;                                                         \
    asn1_start_tag(&state, &tag, kAsn1TagNumberSequence);                   \
    EXPECT_EQ(state.error, kErrorOk);                                       \
    asn1_push_bytes(&state, &tmp[0], tmp.size());                           \
    EXPECT_EQ(state.error, kErrorOk);                                       \
    asn1_finish_tag(&tag);                                                  \
    EXPECT_EQ(state.error, kErrorOk);                                       \
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
