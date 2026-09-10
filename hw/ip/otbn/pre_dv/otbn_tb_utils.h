// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_OTBN_PRE_DV_OTBN_TB_UTILS_H_
#define OPENTITAN_HW_IP_OTBN_PRE_DV_OTBN_TB_UTILS_H_

// Shared utilities for OTBN Verilator testbenches.
// Include this header AFTER defining kWidth and kShareMask in the including TU.

#include <cstdint>

// Floor-log2: equals $clog2(n) for power-of-two values.
constexpr int clog2(int n) { return n <= 1 ? 0 : 1 + clog2(n >> 1); }

// Half-clock periods before reset is released (rising edge at this time).
static constexpr int kRstHalfClk = 20;

// Advance the simulation by one full clock cycle. Leaves clk_i=0.
template <typename Dut>
static void tick(Dut *dut, VerilatedVcdC *vcd, VerilatedContext *ctx) {
  dut->clk_i = 1;
  dut->eval();
  vcd->dump(ctx->time());
  ctx->timeInc(1);
  dut->clk_i = 0;
  dut->eval();
  vcd->dump(ctx->time());
  ctx->timeInc(1);
}

// Tick the clock until rst_ni is released. Leaves clk_i=0, rst_ni=1.
template <typename Dut>
static void run_reset(Dut *dut, VerilatedVcdC *vcd, VerilatedContext *ctx) {
  while (!dut->rst_ni) {
    dut->clk_i = 1;
    if (ctx->time() == kRstHalfClk)
      dut->rst_ni = 1;
    dut->eval();
    vcd->dump(ctx->time());
    ctx->timeInc(1);
    dut->clk_i = 0;
    dut->eval();
    vcd->dump(ctx->time());
    ctx->timeInc(1);
  }
}

// Derived constants for the adder pipeline randomness bus.
static constexpr int kStages = clog2(kWidth);
static constexpr int kRandWidth = 2 * (kStages * kWidth + 1);
static constexpr int kRandWords = (kRandWidth + 31) / 32;

// Extract a kWidth-bit share `share` (0 or 1) from a Verilator-packed
// [NumShares-1:0][kWidth-1:0] port, viewed as a flat little-endian uint32_t[].
static uint32_t get_share(const uint32_t *words, int share) {
  const int lo_bit = share * kWidth;
  const int lo_word = lo_bit / 32;
  const int lo_shift = lo_bit % 32;
  uint64_t bits = (uint64_t)words[lo_word];
  if (lo_shift + kWidth > 32)
    bits |= (uint64_t)words[lo_word + 1] << 32;
  return (uint32_t)((bits >> lo_shift) & kShareMask);
}

// Write a kWidth-bit value into share `share` of a flat uint32_t[].
static void set_share(uint32_t *words, int share, uint32_t val) {
  const int lo_bit = share * kWidth;
  const int lo_word = lo_bit / 32;
  const int lo_shift = lo_bit % 32;
  const uint64_t mask = (uint64_t)kShareMask << lo_shift;
  uint64_t cur = (uint64_t)words[lo_word];
  if (lo_shift + kWidth > 32)
    cur |= (uint64_t)words[lo_word + 1] << 32;
  cur = (cur & ~mask) | ((uint64_t)(val & kShareMask) << lo_shift);
  words[lo_word] = (uint32_t)cur;
  if (lo_shift + kWidth > 32)
    words[lo_word + 1] = (uint32_t)(cur >> 32);
}

#endif  // OPENTITAN_HW_IP_OTBN_PRE_DV_OTBN_TB_UTILS_H_
