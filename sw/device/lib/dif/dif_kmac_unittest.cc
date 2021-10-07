// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace dif_kmac_unittest {
namespace {
using ::testing::ElementsAre;

TEST(CustomizationStringTest, Encode) {
  dif_kmac_customization_string_t cs;

  EXPECT_EQ(dif_kmac_customization_string_init(nullptr, 0, &cs), kDifOk);
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_EQ(dif_kmac_customization_string_init("", 0, &cs), kDifOk);
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_EQ(dif_kmac_customization_string_init("\x00\x00", 2, &cs), kDifOk);
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 16));
  EXPECT_THAT(std::string(&cs.buffer[2], 2), ElementsAre(0, 0));

  EXPECT_EQ(dif_kmac_customization_string_init("SHA-3", 5, &cs), kDifOk);
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 40));
  EXPECT_EQ(std::string(&cs.buffer[2], 5), "SHA-3");

  std::string max(kDifKmacMaxCustomizationStringLen, 0x12);
  EXPECT_EQ(dif_kmac_customization_string_init(max.data(), max.size(), &cs),
            kDifOk);
  static_assert(kDifKmacMaxCustomizationStringLen == 32,
                "encoding needs to be updated");
  EXPECT_THAT(std::string(&cs.buffer[0], 3), ElementsAre(2, 1, 0));
  EXPECT_EQ(std::string(&cs.buffer[3], max.size()), max);
}

TEST(CustomizationStringTest, BadArg) {
  EXPECT_EQ(dif_kmac_customization_string_init("", 0, nullptr), kDifBadArg);

  dif_kmac_customization_string_t cs;
  EXPECT_EQ(dif_kmac_customization_string_init(nullptr, 1, &cs), kDifBadArg);
  EXPECT_EQ(dif_kmac_customization_string_init(
                "", kDifKmacMaxCustomizationStringLen + 1, &cs),
            kDifBadArg);
  EXPECT_EQ(dif_kmac_customization_string_init("", -1, &cs), kDifBadArg);
}

TEST(FunctionNameTest, Encode) {
  dif_kmac_function_name_t fn;

  EXPECT_EQ(dif_kmac_function_name_init(nullptr, 0, &fn), kDifOk);
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_EQ(dif_kmac_function_name_init("", 0, &fn), kDifOk);
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_EQ(dif_kmac_function_name_init("\x00\x00", 2, &fn), kDifOk);
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 16));
  EXPECT_THAT(std::string(&fn.buffer[2], 2), ElementsAre(0, 0));

  EXPECT_EQ(dif_kmac_function_name_init("KMAC", 4, &fn), kDifOk);
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 32));
  EXPECT_EQ(std::string(&fn.buffer[2], 4), "KMAC");

  std::string max(kDifKmacMaxFunctionNameLen, 0x34);
  EXPECT_EQ(dif_kmac_function_name_init(max.data(), max.size(), &fn), kDifOk);
  static_assert(kDifKmacMaxFunctionNameLen == 4,
                "encoding needs to be updated");
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 32));
  EXPECT_EQ(std::string(&fn.buffer[2], max.size()), max);
}

TEST(FunctionNameTest, BadArg) {
  EXPECT_EQ(dif_kmac_function_name_init("", 0, nullptr), kDifBadArg);

  dif_kmac_function_name_t fn;
  EXPECT_EQ(dif_kmac_function_name_init(nullptr, 1, &fn), kDifBadArg);
  EXPECT_EQ(
      dif_kmac_function_name_init("", kDifKmacMaxFunctionNameLen + 1, &fn),
      kDifBadArg);
  EXPECT_EQ(dif_kmac_function_name_init("", -1, &fn), kDifBadArg);
}

}  // namespace
}  // namespace dif_kmac_unittest
