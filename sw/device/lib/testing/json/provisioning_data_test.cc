// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/provisioning_data.h"

#include <cstdio>
#include <cstring>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <iostream>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/test_helpers.h"
#include "sw/device/lib/ujson/ujson.h"

namespace {

using test_helpers::SourceSink;

TEST(OptionalField, ManufCertgenInputsSerializeAllFieldsPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(inputs.dice_auth_key_key_id, 0xaf,
              sizeof(inputs.dice_auth_key_key_id));
  std::memset(inputs.ext_auth_key_key_id, 0xfa,
              sizeof(inputs.ext_auth_key_key_id));
  std::memset(inputs.dice_mldsa_auth_key_key_id, 0xbe,
              sizeof(inputs.dice_mldsa_auth_key_key_id));
  inputs.generate_mldsa_uds_cert = 0x01;

  SourceSink s;
  ujson_t uj = s.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_EQ(
      s.Sink(),
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"dice_mldsa_auth_key_key_id":[190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190],"generate_mldsa_uds_cert":1})json");
}

TEST(OptionalField, ManufCertgenInputsDeserializeAllFieldsPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(&inputs, 0xff, sizeof(inputs));
  SourceSink s(
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"dice_mldsa_auth_key_key_id":[190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190],"generate_mldsa_uds_cert":1})json");
  ujson_t uj = s.UJson();
  EXPECT_TRUE(
      status_ok(ujson_deserialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_THAT(
      inputs.dice_auth_key_key_id,
      testing::Contains(0xaf).Times(sizeof(inputs.dice_auth_key_key_id)));
  EXPECT_THAT(
      inputs.ext_auth_key_key_id,
      testing::Contains(0xfa).Times(sizeof(inputs.ext_auth_key_key_id)));
  EXPECT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0xbe).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  EXPECT_EQ(inputs.generate_mldsa_uds_cert, 1);
}

TEST(OptionalField, ManufCertgenInputsSerializeIntNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(inputs.dice_auth_key_key_id, 0xaf,
              sizeof(inputs.dice_auth_key_key_id));
  std::memset(inputs.ext_auth_key_key_id, 0xfa,
              sizeof(inputs.ext_auth_key_key_id));
  std::memset(inputs.dice_mldsa_auth_key_key_id, 0xbe,
              sizeof(inputs.dice_mldsa_auth_key_key_id));
  inputs.generate_mldsa_uds_cert = 0x00;

  SourceSink s;
  ujson_t uj = s.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_EQ(
      s.Sink(),
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"dice_mldsa_auth_key_key_id":[190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190]})json");
}

TEST(OptionalField, ManufCertgenInputsDeserializeIntNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(&inputs, 0xff, sizeof(inputs));
  ASSERT_EQ(inputs.generate_mldsa_uds_cert, 0xff);
  SourceSink s(
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"dice_mldsa_auth_key_key_id":[190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190,190]})json");
  ujson_t uj = s.UJson();
  EXPECT_TRUE(
      status_ok(ujson_deserialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_THAT(
      inputs.dice_auth_key_key_id,
      testing::Contains(0xaf).Times(sizeof(inputs.dice_auth_key_key_id)));
  EXPECT_THAT(
      inputs.ext_auth_key_key_id,
      testing::Contains(0xfa).Times(sizeof(inputs.ext_auth_key_key_id)));
  EXPECT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0xbe).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  EXPECT_EQ(inputs.generate_mldsa_uds_cert, 0);
}

TEST(OptionalField, ManufCertgenInputsSerializeIntArrayNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(inputs.dice_auth_key_key_id, 0xaf,
              sizeof(inputs.dice_auth_key_key_id));
  std::memset(inputs.ext_auth_key_key_id, 0xfa,
              sizeof(inputs.ext_auth_key_key_id));
  std::memset(inputs.dice_mldsa_auth_key_key_id, 0x00,
              sizeof(inputs.dice_mldsa_auth_key_key_id));
  inputs.generate_mldsa_uds_cert = 0x01;

  SourceSink s;
  ujson_t uj = s.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_EQ(
      s.Sink(),
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"generate_mldsa_uds_cert":1})json");
}

TEST(OptionalField, ManufCertgenInputsDeserializeIntArrayNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(&inputs, 0xff, sizeof(inputs));
  ASSERT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0xff).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  SourceSink s(
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250],"generate_mldsa_uds_cert":1})json");
  ujson_t uj = s.UJson();
  EXPECT_TRUE(
      status_ok(ujson_deserialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_THAT(
      inputs.dice_auth_key_key_id,
      testing::Contains(0xaf).Times(sizeof(inputs.dice_auth_key_key_id)));
  EXPECT_THAT(
      inputs.ext_auth_key_key_id,
      testing::Contains(0xfa).Times(sizeof(inputs.ext_auth_key_key_id)));
  EXPECT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0x00).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  EXPECT_EQ(inputs.generate_mldsa_uds_cert, 1);
}

TEST(OptionalField,
     ManufCertgenInputsSerializeOptionalIntAndIntArrayNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(inputs.dice_auth_key_key_id, 0xaf,
              sizeof(inputs.dice_auth_key_key_id));
  std::memset(inputs.ext_auth_key_key_id, 0xfa,
              sizeof(inputs.ext_auth_key_key_id));
  std::memset(inputs.dice_mldsa_auth_key_key_id, 0x00,
              sizeof(inputs.dice_mldsa_auth_key_key_id));
  inputs.generate_mldsa_uds_cert = 0x00;

  SourceSink s;
  ujson_t uj = s.UJson();
  EXPECT_TRUE(status_ok(ujson_serialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_EQ(
      s.Sink(),
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250]})json");
}

TEST(OptionalField, ManufCertgenInputsDeserializeIntAndIntArrayNotPresent) {
  manuf_certgen_inputs_t inputs;
  std::memset(&inputs, 0xff, sizeof(inputs));
  ASSERT_EQ(inputs.generate_mldsa_uds_cert, 0xff);
  ASSERT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0xff).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  SourceSink s(
      R"json({"dice_auth_key_key_id":[175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175,175],"ext_auth_key_key_id":[250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250,250]})json");
  ujson_t uj = s.UJson();
  EXPECT_TRUE(
      status_ok(ujson_deserialize_manuf_certgen_inputs_t(&uj, &inputs)));
  EXPECT_THAT(
      inputs.dice_auth_key_key_id,
      testing::Contains(0xaf).Times(sizeof(inputs.dice_auth_key_key_id)));
  EXPECT_THAT(
      inputs.ext_auth_key_key_id,
      testing::Contains(0xfa).Times(sizeof(inputs.ext_auth_key_key_id)));
  EXPECT_THAT(
      inputs.dice_mldsa_auth_key_key_id,
      testing::Contains(0x00).Times(sizeof(inputs.dice_mldsa_auth_key_key_id)));
  EXPECT_EQ(inputs.generate_mldsa_uds_cert, 0);
}

}  // namespace
