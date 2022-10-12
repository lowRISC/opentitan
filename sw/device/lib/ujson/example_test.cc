// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ujson/example.h"

#include <cstring>
#include <gtest/gtest.h>
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
}

TEST(Derive, FooDeserialize) {
  foo expected = {-5, 150000, "Kilroy was here"};
  foo foo{};
  SourceSink ss(
      R"json({"foo":-5,"bar":150000,"message":"Kilroy was here"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
}

TEST(Derive, FooDeserializeNoFoo) {
  foo expected = {0, 150000, "Kilroy was here"};
  foo foo{};
  SourceSink ss(R"json({"bar":150000,"message":"Kilroy was here"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
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
}

TEST(Derive, FooDeserializeMessageToLong) {
  foo expected = {-5, 150000, "abcdefghijklmnopqrs"};
  foo foo{};
  SourceSink ss(
      R"json({"foo":-5,"bar":150000,"message":"abcdefghijklmnopqrstuvwxyz"})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_foo(&uj, &foo)));
  EXPECT_EQ(memcmp(&foo, &expected, sizeof(foo)), 0);
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
}

TEST(Derive, RectDeserialize) {
  rect expected = {{10, 20}, {30, 40}};
  rect r{};
  SourceSink ss(
      R"json({"top_left":{"x":10,"y":20},"bottom_right":{"x":30,"y":40}})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_rect(&uj, &r)));
  EXPECT_EQ(memcmp(&r, &expected, sizeof(r)), 0);
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
}

TEST(Derive, MatrixDeserialize) {
  matrix expected = {
      {{0, 1, 0, 0, 0}, {2, 3, 4, 5, 0}, {-1, 0, 0, 0, 0}},
  };
  matrix m{};
  SourceSink ss(R"json({"k":[[0,1],[2, 3, 4, 5],[-1]]})json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_matrix(&uj, &m)));
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

  ss.Reset();
  d = kDirectionSouth;
  EXPECT_TRUE(status_ok(ujson_serialize_direction(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("South")json");

  ss.Reset();
  d = static_cast<direction>(120);
  EXPECT_TRUE(status_ok(ujson_serialize_direction(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json({"IntValue":120})json");
}

TEST(Derive, DirectionDeserialize) {
  direction d;
  SourceSink ss(R"json("West")json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, kDirectionWest);

  ss.Reset(R"json("North")json");
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, kDirectionNorth);

  ss.Reset(R"json({"IntValue":35})json");
  EXPECT_TRUE(status_ok(ujson_deserialize_direction(&uj, &d)));
  EXPECT_EQ(d, static_cast<direction>(35));
}

TEST(Derive, FuzzyBoolSerialize) {
  fuzzy_bool d = kFuzzyBoolTrue;
  SourceSink ss;
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("True")json");

  ss.Reset();
  d = kFuzzyBoolFalse;
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json("False")json");

  ss.Reset();
  d = static_cast<fuzzy_bool>(75);
  EXPECT_TRUE(status_ok(ujson_serialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(ss.Sink(), R"json(75)json");
}

TEST(Derive, FuzzyBoolDeserialize) {
  fuzzy_bool d;
  SourceSink ss(R"json("False")json");
  ujson_t uj = ss.UJson();
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, kFuzzyBoolFalse);

  ss.Reset(R"json("True")json");
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, kFuzzyBoolTrue);

  ss.Reset(R"json(35)json");
  EXPECT_TRUE(status_ok(ujson_deserialize_fuzzy_bool(&uj, &d)));
  EXPECT_EQ(d, static_cast<fuzzy_bool>(35));
}

}  // namespace
