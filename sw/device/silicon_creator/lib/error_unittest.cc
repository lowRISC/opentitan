// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/error.h"

#include <climits>
#include <cstdint>
#include <map>
#include <string>

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"

namespace error_unittest {
namespace {

constexpr int kMinimumHammingDistance = 6;

const std::map<std::string, uint32_t> &GetErrorMap() {
#define STRINGIFY(x) #x
#define ERROR_MAP_INIT(name, value) \
  { STRINGIFY(name), value }
  static std::map<std::string, uint32_t> errors = {
      DEFINE_ERRORS(ERROR_MAP_INIT),
  };
  return errors;
}

rom_error_t ReturnIfError(rom_error_t value) {
  RETURN_IF_ERROR(value);

  // Return something other than kErrorOk just in case RETURN_IF_ERROR
  // was wrong.
  return static_cast<rom_error_t>(0);
}

int HammingDistance(uint32_t a, uint32_t b) {
  // The hamming distance is the number of bits different between the two words.
  return bitfield_popcount32(a ^ b);
}

// Checks that there are no duplicate values in the error definitions.
TEST(ErrorsTest, NoDuplicateValues) {
  const auto &errors = GetErrorMap();

  for (auto a = errors.begin(); a != errors.end(); ++a) {
    for (auto b = a; b != errors.end(); ++b) {
      if (a == b) {
        continue;
      }
      EXPECT_NE(a->second, b->second)
          << "Error codes '" << a->first << "' and '" << b->first
          << "' have the same value.";
    }
  }
}

// Checks that the RETURN_IF_ERROR macro works as expected.
TEST(ErrorsTest, CheckReturnIfError) {
  EXPECT_EQ(kErrorUnknown, ReturnIfError(kErrorUnknown));

  rom_error_t ok = ReturnIfError(kErrorOk);
  EXPECT_EQ(0, static_cast<int>(ok));
}

TEST(ErrorsTest, CheckHammingDistanceToOk) {
  const auto &errors = GetErrorMap();
  int max_distance = 0;
  int min_distance = INT_MAX;
  int distance;

  for (const auto &a : errors) {
    if (a.second == kErrorOk) {
      distance = HammingDistance(a.second, 0);
      std::cout << "Hamming distance between '" << a.first
                << "' and zero: " << distance << std::endl;
    } else {
      distance = HammingDistance(a.second, kErrorOk);
      std::cout << "Hamming distance between '" << a.first
                << "' and kErrorOk: " << distance << std::endl;
    }
    EXPECT_GE(distance, kMinimumHammingDistance);
    min_distance = std::min(min_distance, distance);
    max_distance = std::max(max_distance, distance);
  }
  std::cout << "Minimum hamming distance observed: " << min_distance
            << std::endl;
  std::cout << "Maximum hamming distance observed: " << max_distance
            << std::endl;
}

}  // namespace
}  // namespace error_unittest
