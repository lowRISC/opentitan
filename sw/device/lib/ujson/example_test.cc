// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ujson/example.h"

#include <algorithm>
#include <array>
#include <cstring>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <optional>
#include <string>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/test_helpers.h"
#include "sw/device/lib/ujson/ujson.h"
namespace {
using test_helpers::SourceSink;

TEST(Derive, FooSerialize) {
  foo foo = {-5, 150000, "Kilroy was here"};
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_foo(&uj, &foo)));
  EXPECT_EQ(ss.Sink(),
            R"json({"foo":-5,"bar":150000,"message":"Kilroy was here"})json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x1e31c20e);
}

TEST(Derive, FooDeserialize) {
  foo expected = {-5, 150000, "Kilroy was here"};
  foo foo{};
  SourceSink ss(
      R"json({"foo":-5,"bar":150000,"message":"Kilroy was here"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x1e31c20e);
}

TEST(Derive, FooDeserializeNoFoo) {
  foo expected = {0, 150000, "Kilroy was here"};
  foo foo{};
  SourceSink ss(R"json({"bar":150000,"message":"Kilroy was here"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x431acc08);
}

TEST(Derive, FooDeserializeNoMessage) {
  foo expected = {
      -5,
      150000,
  };
  foo foo{};
  SourceSink ss(R"json({"foo":-5,"bar":150000})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xded4ce6);
}

TEST(Derive, FooDeserializeMessageToLong) {
  foo expected = {-5, 150000, "abcdefghijklmnopqrs"};
  foo foo{};
  SourceSink ss(
      R"json({"foo":-5,"bar":150000,"message":"abcdefghijklmnopqrstuvwxyz"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xfaebc314);
}

TEST(Derive, FooDeserializeBogusKey) {
  foo foo{};
  SourceSink ss(
      R"json({"bar":150000,"message":"Kilroy was here","bogus":99})json");
  ujson_t uj = ss.UJson();
  EXPECT_EQ(status_err(ujson_deserialize_foo(&uj, &foo)), kInvalidArgument);
}

TEST(Derive, RectSerialize) {
  rect r = {{10, 10}, {60, 40}};
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_rect(&uj, &r)));
  EXPECT_EQ(
      ss.Sink(),
      R"json({"top_left":{"x":10,"y":10},"bottom_right":{"x":60,"y":40}})json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x4b9a0fb1);
}

TEST(Derive, RectDeserialize) {
  rect expected = {{10, 20}, {30, 40}};
  rect r{};
  SourceSink ss(
      R"json({"top_left":{"x":10,"y":20},"bottom_right":{"x":30,"y":40}})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_rect(&uj, &r)));
  EXPECT_EQ(memcmp(&r, &expected, sizeof(r)), 0);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xb11e9dea);
}

TEST(Derive, MatrixSerialize) {
  matrix m = {
      {{0, 1, 2, 3, 4}, {5, 6, 7, 8, 9}, {-1, -2, -3, -4, -5}},
  };
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_matrix(&uj, &m)));
  EXPECT_EQ(ss.Sink(),
            R"json({"k":[[0,1,2,3,4],[5,6,7,8,9],[-1,-2,-3,-4,-5]]})json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x927a936);
}

TEST(Derive, MatrixDeserialize) {
  matrix expected = {
      {{0, 1, 0, 0, 0}, {2, 3, 4, 5, 0}, {-1, 0, 0, 0, 0}},
  };
  matrix m{};
  SourceSink ss(R"json({"k":[[0,1],[2, 3, 4, 5],[-1]]})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_matrix(&uj, &m)));
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xca69b105);
  ujson_serialize_matrix(&uj, &m);
  std::cout << ss.Sink() << "\n\n";
  EXPECT_EQ(memcmp(&m, &expected, sizeof(m)), 0);
}

TEST(Derive, DirectionSerialize) {
  direction d = kDirectionEast;
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_direction(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("East")json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x20ab69de);

  ss.Reset();
  ujson_crc32_reset(&uj);
  d = kDirectionSouth;
  EXPECT_TRUE(status_ok(ujson_serialize_direction(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("South")json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x236b5d67);

  ss.Reset();
  ujson_crc32_reset(&uj);
  d = static_cast<direction>(120);
  EXPECT_TRUE(status_ok(ujson_serialize_direction(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json({"IntValue":120})json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x63cb5f57);
}

TEST(Derive, DirectionDeserialize) {
  direction d;
  SourceSink ss(R"json("West")json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, kDirectionWest);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xb5e93a6b);

  ss.Reset(R"json("North")json");
  ujson_crc32_reset(&uj);
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, kDirectionNorth);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x1f4749b);

  ss.Reset(R"json({"IntValue":35})json");
  ujson_crc32_reset(&uj);
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, static_cast<direction>(35));
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x86f181c2);
}

TEST(Derive, FuzzyBoolSerialize) {
  fuzzy_bool d = kFuzzyBoolTrue;
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("True")json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x68d3703f);

  ss.Reset();
  ujson_crc32_reset(&uj);
  d = kFuzzyBoolFalse;
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("False")json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x52b000f3);

  ss.Reset();
  ujson_crc32_reset(&uj);
  d = static_cast<fuzzy_bool>(75);
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json(75)json");
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x876d76e8);
}

TEST(Derive, FuzzyBoolDeserialize) {
  fuzzy_bool d;
  SourceSink ss(R"json("False")json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, kFuzzyBoolFalse);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x52b000f3);

  ujson_crc32_reset(&uj);
  ss.Reset(R"json("True")json");
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, kFuzzyBoolTrue);
  EXPECT_EQ(ujson_crc32_finish(&uj), 0x68d3703f);

  ujson_crc32_reset(&uj);
  ss.Reset(R"json(35)json");
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, static_cast<fuzzy_bool>(35));
  EXPECT_EQ(ujson_crc32_finish(&uj), 0xe301b3ec);
}

struct FooOptional1DeriveParam {
  int32_t foo1_val;
  std::array<int32_t, 2> foo2_val;
  const char *message_val;
  std::optional<uint32_t> bar1_val;
  std::optional<std::array<uint32_t, 2>> bar2_val;
  const char *json_data;
};

class FooOptional1Derive
    : public testing::TestWithParam<FooOptional1DeriveParam> {};

TEST_P(FooOptional1Derive, Serialize) {
  const auto p = GetParam();
  foo_optional_1_t d;
  d.foo1 = p.foo1_val;
  std::copy_n(p.foo2_val.begin(), p.foo2_val.size(), d.foo2);
  std::strncpy(d.message, p.message_val, sizeof(d.message));

  d.has_bar1 = 0;
  if (p.bar1_val.has_value()) {
    d.has_bar1 = 1;
    d.bar1 = *p.bar1_val;
  }

  d.has_bar2 = 0;
  if (p.bar2_val.has_value()) {
    d.has_bar2 = 1;
    std::copy_n(p.bar2_val->begin(), p.bar2_val->size(), d.bar2);
  }

  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_foo_optional_1_t(&uj, &d)));
  EXPECT_EQ(ss.Sink(), p.json_data);
}

TEST_P(FooOptional1Derive, Deserialize) {
  const auto p = GetParam();
  foo_optional_1_t d;
  SourceSink ss(p.json_data);
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo_optional_1_t(&uj, &d)));

  EXPECT_EQ(d.foo1, p.foo1_val);
  EXPECT_THAT(d.foo2, testing::ElementsAreArray(p.foo2_val));
  EXPECT_THAT(d.message, testing::StrEq(p.message_val));

  if (p.bar1_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar1), 0);
    EXPECT_THAT(d.bar1, *p.bar1_val);
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar1), 0);
  }

  if (p.bar2_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar2), 0);
    EXPECT_THAT(d.bar2, testing::ElementsAreArray(*p.bar2_val));
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar2), 0);
  }
}

INSTANTIATE_TEST_SUITE_P(
    FooOptional1SerializeDeserializeTests, FooOptional1Derive,
    testing::Values(
        FooOptional1DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","bar1":654,"bar2":[321,987]})json",
        },
        FooOptional1DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 0,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({0, 0}),
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","bar1":0,"bar2":[0,0]})json",
        },
        FooOptional1DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","bar2":[321,987]})json",
        },
        FooOptional1DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","bar1":654})json",
        },
        FooOptional1DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        }));

struct FooOptional2DeriveParam {
  int32_t foo1_val;
  std::array<int32_t, 2> foo2_val;
  const char *message_val;
  std::optional<uint32_t> bar1_val;
  std::optional<std::array<uint32_t, 2>> bar2_val;
  const char *json_data;
};

class FooOptional2Derive
    : public testing::TestWithParam<FooOptional2DeriveParam> {};

TEST_P(FooOptional2Derive, Serialize) {
  const auto p = GetParam();
  foo_optional_2_t d;
  d.foo1 = p.foo1_val;
  std::copy_n(p.foo2_val.begin(), p.foo2_val.size(), d.foo2);
  std::strncpy(d.message, p.message_val, sizeof(d.message));

  d.has_bar1 = 0;
  if (p.bar1_val.has_value()) {
    d.has_bar1 = 1;
    d.bar1 = *p.bar1_val;
  }

  d.has_bar2 = 0;
  if (p.bar2_val.has_value()) {
    d.has_bar2 = 1;
    std::copy_n(p.bar2_val->begin(), p.bar2_val->size(), d.bar2);
  }

  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_foo_optional_2_t(&uj, &d)));
  EXPECT_EQ(ss.Sink(), p.json_data);
}

TEST_P(FooOptional2Derive, Deserialize) {
  const auto p = GetParam();
  foo_optional_2_t d;
  SourceSink ss(p.json_data);
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo_optional_2_t(&uj, &d)));

  EXPECT_EQ(d.foo1, p.foo1_val);
  EXPECT_THAT(d.foo2, testing::ElementsAreArray(p.foo2_val));
  EXPECT_THAT(d.message, testing::StrEq(p.message_val));

  if (p.bar1_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar1), 0);
    EXPECT_THAT(d.bar1, *p.bar1_val);
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar1), 0);
  }

  if (p.bar2_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar2), 0);
    EXPECT_THAT(d.bar2, testing::ElementsAreArray(*p.bar2_val));
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar2), 0);
  }
}

INSTANTIATE_TEST_SUITE_P(
    FooOptional2SerializeDeserializeTests, FooOptional2Derive,
    testing::Values(
        FooOptional2DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"bar1":654,"bar2":[321,987],"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        },
        FooOptional2DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 0,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({0, 0}),
            .json_data =
                R"json({"bar1":0,"bar2":[0,0],"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        },
        FooOptional2DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"bar2":[321,987],"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        },
        FooOptional2DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"bar1":654,"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        },
        FooOptional2DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!"})json",
        }));

struct FooOptional3DeriveParam {
  int32_t foo1_val;
  std::array<int32_t, 2> foo2_val;
  int32_t foo3_val;
  const char *message_val;
  std::optional<uint32_t> bar1_val;
  std::optional<std::array<uint32_t, 2>> bar2_val;
  const char *json_data;
};

class FooOptional3Derive
    : public testing::TestWithParam<FooOptional3DeriveParam> {};

TEST_P(FooOptional3Derive, Serialize) {
  const auto p = GetParam();
  foo_optional_3_t d;
  d.foo1 = p.foo1_val;
  std::copy_n(p.foo2_val.begin(), p.foo2_val.size(), d.foo2);
  std::strncpy(d.message, p.message_val, sizeof(d.message));
  d.foo3 = p.foo3_val;

  d.has_bar1 = 0;
  if (p.bar1_val.has_value()) {
    d.has_bar1 = 1;
    d.bar1 = *p.bar1_val;
  }

  d.has_bar2 = 0;
  if (p.bar2_val.has_value()) {
    d.has_bar2 = 1;
    std::copy_n(p.bar2_val->begin(), p.bar2_val->size(), d.bar2);
  }

  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_foo_optional_3_t(&uj, &d)));
  EXPECT_EQ(ss.Sink(), p.json_data);
}

TEST_P(FooOptional3Derive, Deserialize) {
  const auto p = GetParam();
  foo_optional_3_t d;
  SourceSink ss(p.json_data);
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo_optional_3_t(&uj, &d)));

  EXPECT_EQ(d.foo1, p.foo1_val);
  EXPECT_THAT(d.foo2, testing::ElementsAreArray(p.foo2_val));
  EXPECT_THAT(d.message, testing::StrEq(p.message_val));
  EXPECT_EQ(d.foo3, p.foo3_val);

  if (p.bar1_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar1), 0);
    EXPECT_THAT(d.bar1, *p.bar1_val);
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar1), 0);
  }

  if (p.bar2_val.has_value()) {
    EXPECT_NE(static_cast<uint32_t>(d.has_bar2), 0);
    EXPECT_THAT(d.bar2, testing::ElementsAreArray(*p.bar2_val));
  } else {
    EXPECT_EQ(static_cast<uint32_t>(d.has_bar2), 0);
  }
}

INSTANTIATE_TEST_SUITE_P(
    FooOptional3SerializeDeserializeTests, FooOptional3Derive,
    testing::Values(
        FooOptional3DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .foo3_val = 150,
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"foo1":456,"bar1":654,"foo2":[123,789],"message":"Hello world!","bar2":[321,987],"foo3":150})json",
        },
        FooOptional3DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .foo3_val = 150,
            .message_val = "Hello world!",
            .bar1_val = 0,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({0, 0}),
            .json_data =
                R"json({"foo1":456,"bar1":0,"foo2":[123,789],"message":"Hello world!","bar2":[0,0],"foo3":150})json",
        },
        FooOptional3DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .foo3_val = 150,
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::make_optional<std::array<uint32_t, 2>>({321, 987}),
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","bar2":[321,987],"foo3":150})json",
        },
        FooOptional3DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .foo3_val = 150,
            .message_val = "Hello world!",
            .bar1_val = 654,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"foo1":456,"bar1":654,"foo2":[123,789],"message":"Hello world!","foo3":150})json",
        },
        FooOptional3DeriveParam{
            .foo1_val = 456,
            .foo2_val = {123, 789},
            .foo3_val = 150,
            .message_val = "Hello world!",
            .bar1_val = std::nullopt,
            .bar2_val = std::nullopt,
            .json_data =
                R"json({"foo1":456,"foo2":[123,789],"message":"Hello world!","foo3":150})json",
        }));

}  // namespace
