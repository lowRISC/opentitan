// Copyright lowRISC contributors (OpenTitan project).
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <random>
#include <stdio.h>

#include "Vcircuit.h"
#include "testbench.h"

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Testbench<Vcircuit> tb;
  tb.opentrace("tmp.vcd");

  // RNG Setup for high-quality entropy
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<uint32_t> dis(0, 0xFFFFFFFF);

  tb.reset();

  // 322 bits requires 11 words of 32-bits (11 * 32 = 352)
  const int NUM_WORDS = 11;
  // Mask for the 11th word (Word 10) to only use 2 bits: (1 << 2) - 1
  const uint32_t LAST_WORD_MASK = 0x3;

  // Initialize the first cycle of randomness
  for (int word = 0; word < NUM_WORDS; word++) {
    if (word == (NUM_WORDS - 1)) {
      tb.m_core.rand_i[word] = dis(gen) & LAST_WORD_MASK;
    } else {
      tb.m_core.rand_i[word] = dis(gen);
    }
  }

  // Drive Combined Shares (A and B)
  // [63:32] = B, [31:0] = A
  tb.m_core.share0_i = 0xDEADBEEFF0F0F0F0ULL;
  tb.m_core.share1_i = 0x0002C001F0F0F0F0ULL;
  tb.m_core.en_i = 0;

  tb.tick();

  tb.m_core.en_i = 0x1;

  // Simulation Run
  for (int i = 0; i < 6; i++) {
    tb.tick();
    tb.m_core.en_i = 0x0;
    for (int word = 0; word < NUM_WORDS; word++) {
      if (word == (NUM_WORDS - 1)) {
        tb.m_core.rand_i[word] = dis(gen) & LAST_WORD_MASK;
      } else {
        tb.m_core.rand_i[word] = dis(gen);
      }
    }
  }

  tb.closetrace();
  return 0;
}
