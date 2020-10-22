// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/hw_sha256.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_main.h"

static const size_t kDataLen = 142;
static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static const uint32_t kExpectedDigest[8] = {0xdc96c23d, 0xaf36e268, 0xcb68ff71,
                                            0xe92f76e2, 0xb8a8379d, 0x426dc745,
                                            0x19f5cff7, 0x4ec9c6d6};

const test_config_t kTestConfig;

bool test_main(void) {
  LOG_INFO("Running SHA256 test");

  uint32_t digest[8];
  hw_SHA256_hash(kData, kDataLen, (uint8_t *)digest);

  for (uint32_t i = 0; i < 8; i++) {
    if (digest[i] != kExpectedDigest[i]) {
      LOG_ERROR("Digest mismatched at index %d: exp: %x, act: %x", i, digest[i],
                kExpectedDigest[i]);
      flash_write_scratch_reg(digest[i]);
      return false;
    }
  }

  return true;
}
