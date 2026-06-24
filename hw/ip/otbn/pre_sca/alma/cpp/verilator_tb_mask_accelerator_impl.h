// Copyright lowRISC contributors (OpenTitan project).
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_MASK_ACCELERATOR_IMPL_H_
#define OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_MASK_ACCELERATOR_IMPL_H_

// Shared testbench implementation for otbn_mask_accelerator_sca_wrapper Alma
// verification.  Include this file after defining:
//
//   MASK_OP      — mask_op_e encoding (uint8_t literal)
//   ARITH_INPUT  — 0 for boolean XOR sharing, 1 for arithmetic additive sharing

#include <random>
#include <stdio.h>

#include "Vcircuit.h"
#include "testbench.h"

// Port widths (Width=32, VecSize=8, Stages=5):
//   RandWidth      = 2*(5*32+1) = 322 bits
//   TotalRandWidth = RandWidth + 2*Width = 322 + 64 = 386 bits -> 13 x 32-bit
//   words
static constexpr int RAND_WORDS = 13;
static constexpr uint32_t RAND_LAST_MASK =
    (1u << 2) - 1;  // 386 mod 32 = 2 bits
static constexpr int VEC_SIZE = 8;

// Pipeline depth: 2 * VecSize + Latency - 1 + margin
static constexpr int NUM_CYCLES = 30;

// ML-DSA-87 prime, used as modulus.
static constexpr uint32_t MODULUS = 8380417u;

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Testbench<Vcircuit> tb;
  tb.opentrace("tmp.vcd");

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<uint32_t> dis(0, 0xFFFFFFFFu);

  auto refresh_rand = [&]() {
    for (int w = 0; w < RAND_WORDS - 1; w++)
      tb.m_core.rand_i[w] = dis(gen);
    tb.m_core.rand_i[RAND_WORDS - 1] = dis(gen) & RAND_LAST_MASK;
  };

  tb.reset();

  tb.m_core.mod_i = MODULUS;
  tb.m_core.mask_op_i = MASK_OP;
  tb.m_core.en_i = 0;

#if ARITH_INPUT
  // Arithmetic masking: share0[k] + share1[k] = secret[k] (mod 2^32)
  for (int k = 0; k < VEC_SIZE; k++) {
    uint32_t a_mask = dis(gen), b_mask = dis(gen);
    tb.m_core.share0_i[2 * k] = a_mask;
    tb.m_core.share0_i[2 * k + 1] = b_mask;
    tb.m_core.share1_i[2 * k] = dis(gen) - a_mask;
    tb.m_core.share1_i[2 * k + 1] = dis(gen) - b_mask;
  }
#else
  // Boolean masking: share0[k] XOR share1[k] = secret[k]
  for (int k = 0; k < VEC_SIZE; k++) {
    uint32_t a_mask = dis(gen), b_mask = dis(gen);
    tb.m_core.share0_i[2 * k] = dis(gen) ^ a_mask;
    tb.m_core.share0_i[2 * k + 1] = dis(gen) ^ b_mask;
    tb.m_core.share1_i[2 * k] = a_mask;
    tb.m_core.share1_i[2 * k + 1] = b_mask;
  }
#endif

  // One idle cycle before asserting enable, then let the wrapper serialise
  // all VecSize elements into the DUT automatically.
  refresh_rand();
  tb.tick();

  tb.m_core.en_i = 1;
  for (int i = 0; i < NUM_CYCLES; i++) {
    refresh_rand();
    tb.tick();
  }

  tb.closetrace();
  return 0;
}

#endif  // OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_MASK_ACCELERATOR_IMPL_H_
