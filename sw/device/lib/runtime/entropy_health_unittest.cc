// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/entropy_health.h"

#include "gtest/gtest.h"

namespace entropy_health_test {
namespace {

TEST(EntropyHealthTest, HappyPath) {
  entropy_health_rct_state_t state;
  entropy_health_rct_init(&state, 0x12345678);

  // Provide an alternating sequence.
  for (int i = 0; i < ENTROPY_HEALTH_RCT_THRESHOLD * 2; ++i) {
    uint32_t symbol = (i % 2 == 0) ? 0xAAAAAAAA : 0x55555555;
    entropy_health_rct_update(&state, symbol);
    EXPECT_FALSE(entropy_health_rct_has_failed(&state));
  }
}

TEST(EntropyHealthTest, StuckAtFault) {
  entropy_health_rct_state_t state;
  uint32_t stuck_symbol = 0x00000000;
  entropy_health_rct_init(&state, stuck_symbol);

  // Inject THRESHOLD - 1 identical symbols.
  // Note: the initialization counts as 1. So we inject THRESHOLD - 2 more.
  for (int i = 0; i < ENTROPY_HEALTH_RCT_THRESHOLD - 2; ++i) {
    entropy_health_rct_update(&state, stuck_symbol);
    EXPECT_FALSE(entropy_health_rct_has_failed(&state));
  }

  // Inject exactly 1 more identical symbol to hit the threshold.
  entropy_health_rct_update(&state, stuck_symbol);
  EXPECT_TRUE(entropy_health_rct_has_failed(&state));
}

TEST(EntropyHealthTest, RecoveryResistance) {
  entropy_health_rct_state_t state;
  uint32_t stuck_symbol = 0xFFFFFFFF;
  entropy_health_rct_init(&state, stuck_symbol);

  // Trigger the fail flag.
  for (int i = 0; i < ENTROPY_HEALTH_RCT_THRESHOLD - 1; ++i) {
    entropy_health_rct_update(&state, stuck_symbol);
  }
  EXPECT_TRUE(entropy_health_rct_has_failed(&state));

  // Inject 100 perfectly random, healthy symbols.
  for (int i = 0; i < 100; ++i) {
    entropy_health_rct_update(&state, i); // Changing symbols
    // Assert that the fail flag remains set.
    EXPECT_TRUE(entropy_health_rct_has_failed(&state));
  }
}

}  // namespace
}  // namespace entropy_health_test
