// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"

#include <ostream>
#include <stdint.h>
#include <tuple>

#include "gtest/gtest.h"

namespace status_unittest {
namespace {

TEST(Status, OkValues) {
  status_t status;

  // The no-argument form should have a value of zero.
  status = OK_STATUS();
  EXPECT_EQ(status_ok(status), true);
  EXPECT_EQ(status_err(status), absl_status_t::kOk);
  EXPECT_EQ(status.value, 0);

  // The one-argument form should have the value of the argument.
  status = OK_STATUS(5);
  EXPECT_EQ(status_ok(status), true);
  EXPECT_EQ(status_err(status), absl_status_t::kOk);
  EXPECT_EQ(status.value, 5);

  // Any negative value for OK is not permitted and will result
  // in an error value.
  status = OK_STATUS(-1);
  EXPECT_EQ(status_ok(status), false);
}

TEST(Status, ErrorValues) {
  int32_t arg;
  status_t status;
  bool err;
  const char *message;
  char mod_id[4]{};

  // The no-argument form should carry the line number on which the error
  // was created and a module-id of the first three letters of the filename.
  status = UNKNOWN();
  int32_t expected_line = __LINE__ - 1;
  err = status_extract(status, &message, &arg, mod_id);
  EXPECT_EQ(status_ok(status), false);
  EXPECT_EQ(status_err(status), absl_status_t::kUnknown);
  EXPECT_EQ(err, true);
  EXPECT_EQ(arg, expected_line);
  EXPECT_EQ(std::string(mod_id), "STA");

  // The one-argument form should carry the value of that argument.
  status = CANCELLED(1);
  err = status_extract(status, &message, &arg, mod_id);
  EXPECT_EQ(status_ok(status), false);
  EXPECT_EQ(status_err(status), absl_status_t::kCancelled);
  EXPECT_EQ(err, true);
  EXPECT_EQ(arg, 1);
  EXPECT_EQ(std::string(mod_id), "STA");
}

}  // namespace
}  // namespace status_unittest
