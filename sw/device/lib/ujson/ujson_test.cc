// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ujson/ujson.h"

#include <gtest/gtest.h>
#include <string>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/test_helpers.h"

namespace {
using test_helpers::SourceSink;

TEST(UJson, GetC) {
  SourceSink ss("abc123");
  ujson_t uj = ss.UJson();

  EXPECT_EQ(ujson_getc(&uj).value, 'a');
  EXPECT_EQ(ujson_getc(&uj).value, 'b');
  EXPECT_EQ(ujson_getc(&uj).value, 'c');
  EXPECT_EQ(status_err(ujson_ungetc(&uj, 'd')), kOk);
  EXPECT_EQ(ujson_getc(&uj).value, 'd');
  EXPECT_EQ(ujson_getc(&uj).value, '1');
  EXPECT_EQ(ujson_getc(&uj).value, '2');
  EXPECT_EQ(ujson_getc(&uj).value, '3');
  EXPECT_EQ(status_err(ujson_getc(&uj)), kResourceExhausted);
}

TEST(UJson, PutBuf) {
  SourceSink ss;
  ujson_t uj = ss.UJson();

  EXPECT_TRUE(status_ok(ujson_putbuf(&uj, "abc", 3)));
  EXPECT_TRUE(status_ok(ujson_putbuf(&uj, "123", 3)));
  EXPECT_EQ(ss.Sink(), "abc123");
}

TEST(UJson, Consume) {
  SourceSink ss("  \t\r\nax");
  ujson_t uj = ss.UJson();

  EXPECT_EQ(status_err(ujson_consume(&uj, 'a')), kOk);
  EXPECT_EQ(status_err(ujson_consume(&uj, 'b')), kNotFound);
}

TEST(UJson, ParseQuotedString) {
  SourceSink ss(R"json(
        "Hello World\r\n"
    )json");
  ujson_t uj = ss.UJson();
  char buf[256];
  status_t s;

  s = ujson_parse_qs(&uj, buf, sizeof(buf));
  EXPECT_TRUE(status_ok(s));
  EXPECT_EQ(s.value, 13);
  std::string vala(buf);
  EXPECT_EQ(vala, "Hello World\r\n");

  ss.Reset();
  s = ujson_parse_qs(&uj, buf, 6);
  EXPECT_TRUE(status_ok(s));
  EXPECT_EQ(s.value, 5);
  std::string valb(buf);
  EXPECT_EQ(valb, "Hello");
}

TEST(UJson, ParseQuotedStringInvalidString) {
  SourceSink ss("abc");
  ujson_t uj = ss.UJson();
  char buf[256];
  status_t s;

  s = ujson_parse_qs(&uj, buf, sizeof(buf));
  EXPECT_EQ(status_err(s), kNotFound);
}

TEST(UJson, ParseQuotedStringShortBuffer) {
  SourceSink ss("\"abc");
  ujson_t uj = ss.UJson();
  char buf[256];
  status_t s;

  s = ujson_parse_qs(&uj, buf, sizeof(buf));
  EXPECT_EQ(status_err(s), kResourceExhausted);
}

TEST(UJson, ParseBoolean) {
  SourceSink ss("true");
  ujson_t uj = ss.UJson();
  status_t s;
  bool val = false;

  // Parse the token "true".
  s = ujson_deserialize_bool(&uj, &val);
  EXPECT_TRUE(status_ok(s));
  EXPECT_TRUE(val);

  // Parse the token "false".
  ss.Reset("false");
  val = true;
  s = ujson_deserialize_bool(&uj, &val);
  EXPECT_TRUE(status_ok(s));
  EXPECT_FALSE(val);

  // Check various non-true/false values.
  ss.Reset("xyz");
  s = ujson_deserialize_bool(&uj, &val);
  EXPECT_FALSE(status_ok(s));
  ss.Reset("trust");
  s = ujson_deserialize_bool(&uj, &val);
  EXPECT_FALSE(status_ok(s));
  ss.Reset("fast");
  s = ujson_deserialize_bool(&uj, &val);
  EXPECT_FALSE(status_ok(s));
}

#define INT(type_, str_, value_)                                  \
  do {                                                            \
    SourceSink ss(str_);                                          \
    ujson_t uj = ss.UJson();                                      \
    type_ t;                                                      \
    status_t s = ujson_parse_integer(&uj, (void *)&t, sizeof(t)); \
    EXPECT_EQ(status_err(s), kOk);                                \
    EXPECT_EQ(t, value_);                                         \
  } while (0)

#define SIMPLE_INT(type_, value_) INT(type_, #value_, value_)

TEST(UJson, ParseInteger) {
  SIMPLE_INT(int64_t, -1);
  SIMPLE_INT(uint64_t, 9223372036854775808);
  SIMPLE_INT(uint32_t, 12345678);
  SIMPLE_INT(int32_t, -12345678);
  SIMPLE_INT(int16_t, -1);
  SIMPLE_INT(int8_t, -1);

  // Won't fit, we should get zero.
  INT(uint8_t, "256", 0);
  // This value overflows int64 and becomes its own negative.
  INT(int64_t, "9223372036854775808", -9223372036854775808);
}
#undef INT
#undef SIMPLE_INT

TEST(UJson, ParseIntegerError) {
  SourceSink ss;
  ujson uj = ss.UJson();
  uint32_t t;
  status_t s;

  // Empty string.
  s = ujson_parse_integer(&uj, (void *)&t, sizeof(t));
  EXPECT_EQ(status_err(s), kResourceExhausted);

  // Non integer character.
  ss.Reset("q");
  s = ujson_parse_integer(&uj, (void *)&t, sizeof(t));
  EXPECT_EQ(status_err(s), kNotFound);
}

TEST(UJson, SerializeString) {
  SourceSink ss;
  ujson uj = ss.UJson();

  EXPECT_TRUE(status_ok(ujson_serialize_string(&uj, "abc123")));
  EXPECT_EQ(ss.Sink(), R"json("abc123")json");

  ss.Reset();
  EXPECT_TRUE(status_ok(ujson_serialize_string(&uj, "\"\\\b\f\n\r\t")));
  EXPECT_EQ(ss.Sink(), R"json("\"\\\b\f\n\r\t")json");

  ss.Reset();
  EXPECT_TRUE(status_ok(ujson_serialize_string(&uj, "\xFF\x01\x99")));
  EXPECT_EQ(ss.Sink(), R"json("\u00ff\u0001\u0099")json");
}

TEST(UJson, SerializeBool) {
  SourceSink ss;
  ujson uj = ss.UJson();
  bool val;

  val = true;
  EXPECT_TRUE(status_ok(ujson_serialize_bool(&uj, &val)));
  EXPECT_EQ(ss.Sink(), R"json(true)json");

  ss.Reset();
  val = false;
  EXPECT_TRUE(status_ok(ujson_serialize_bool(&uj, &val)));
  EXPECT_EQ(ss.Sink(), R"json(false)json");
}

#define INT(type_, str_, value_)                   \
  do {                                             \
    SourceSink ss;                                 \
    ujson_t uj = ss.UJson();                       \
    type_ t = value_;                              \
    status_t s = ujson_serialize_##type_(&uj, &t); \
    EXPECT_EQ(status_err(s), kOk);                 \
    EXPECT_EQ(ss.Sink(), str_);                    \
  } while (0)

TEST(UJson, SerializeIntegers) {
  INT(uint64_t, "9223372036854775808", 1UL << 63);
  INT(uint32_t, "4294967295", 0xFFFFFFFF);
  INT(uint16_t, "32768", 0x8000);
  INT(uint8_t, "129", 129);

  INT(int64_t, "-9223372036854775808", 1UL << 63);
  INT(int32_t, "-1", 0xFFFFFFFF);
  INT(int16_t, "-32768", 0x8000);
  INT(int8_t, "-2", 0xfe);
}

TEST(UJson, SerializeStatus) {
  SourceSink ss;
  ujson uj = ss.UJson();
  status_t val;

  val = OK_STATUS(1234);
  EXPECT_TRUE(status_ok(ujson_serialize_status_t(&uj, &val)));
  EXPECT_EQ(ss.Sink(), R"json({"Ok":1234})json");
}

TEST(UJson, DeerializeStatus) {
  SourceSink ss(R"json({"Ok":1234})json");
  ujson uj = ss.UJson();
  status_t val;
  const char *code;
  char mod_id[4] = {0};
  int32_t arg;

  // Parse an Ok value with an argument.
  EXPECT_TRUE(status_ok(ujson_deserialize_status_t(&uj, &val)));
  OT_DISCARD(status_extract(val, &code, &arg, mod_id));
  EXPECT_EQ(status_err(val), kOk);
  EXPECT_EQ(arg, 1234);

  // Parse an error value with a module and argument.
  // The module_id should get truncated to 3 characters.
  ss.Reset(R"json({"InvalidArgument": ["foobar", 77]})json");
  EXPECT_TRUE(status_ok(ujson_deserialize_status_t(&uj, &val)));
  OT_DISCARD(status_extract(val, &code, &arg, mod_id));
  EXPECT_EQ(status_err(val), kInvalidArgument);
  EXPECT_EQ(std::string(mod_id), "FOO");
  EXPECT_EQ(arg, 77);
}

}  // namespace
