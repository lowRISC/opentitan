// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstdint>
#include <cstdio>
#include <queue>
#include <random>

#include "Votbn_sec_add.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

// Width of each adder input in bits.
// This testbench has only been run with Width as 4, 8, 16 or 32.
// Override at compile time with -DWIDTH=<n> (e.g. -DWIDTH=16).
#ifndef WIDTH
#define WIDTH 32
#endif

static constexpr int kWidth = WIDTH;
static_assert(kWidth >= 4 && kWidth <= 32,
              "Testbench only supports 4 <= Width <= 32.");

// Mask to restrict random stimulus values to kWidth bits.
static constexpr uint32_t kShareMask =
    (kWidth == 32) ? ~0u : ((1u << kWidth) - 1);

#include "otbn_tb_utils.h"

// Mask for a single (kWidth+1)-bit result share (carry included).
static constexpr uint64_t kResultMask = (2ULL << kWidth) - 1;
static constexpr int kTotStims = 1'000'000;

// Extract one (kWidth+1)-bit share from result_o[1:0][kWidth:0] viewed as
// uint32_t[].
static uint64_t result_share(const uint32_t *r, int share) {
  const int lo_word = (share * (kWidth + 1)) / 32;
  const int lo_shift = (share * (kWidth + 1)) % 32;
  uint64_t bits = (uint64_t)r[lo_word];
  if (lo_shift + kWidth + 1 > 32)
    bits |= (uint64_t)r[lo_word + 1] << 32;
  return (bits >> lo_shift) & kResultMask;
}

int main(int argc, char **argv) {
  VerilatedContext *const contextp = new VerilatedContext;
  contextp->commandArgs(argc, argv);
  contextp->traceEverOn(true);

  Votbn_sec_add *const dut = new Votbn_sec_add(contextp, "TOP");

  // Access Verilator packed [N:0][W-1:0] ports as flat uint32_t[]
  // (little-endian).
  uint32_t *const rand_raw = reinterpret_cast<uint32_t *>(&dut->rand_i);
  uint32_t *const inp1_raw = reinterpret_cast<uint32_t *>(&dut->inp1_i);
  uint32_t *const inp2_raw = reinterpret_cast<uint32_t *>(&dut->inp2_i);
  uint32_t *const result_raw = reinterpret_cast<uint32_t *>(&dut->result_o);

  // VCD waveform writer; receives signal snapshots on each vcd->dump() call.
  VerilatedVcdC *const vcd = new VerilatedVcdC;
  dut->trace(vcd, 99);
  vcd->open("dump.vcd");

  // Mersenne Twister RNG with a fixed seed for deterministic, reproducible
  // stimulus.
  std::mt19937 rng(42);
  // Produces uniformly distributed random uint32_t values (full 32-bit range).
  std::uniform_int_distribution<uint32_t> dist;

  // FIFO of expected (kWidth+1)-bit results. Each entry is pushed when a
  // stimulus is driven and popped when the corresponding valid_o fires,
  // absorbing the pipeline latency.
  std::queue<uint64_t> exp_queue;
  int n_stims = 0, n_checks = 0, n_errs = 0;

  // Initialise all inputs to a known state before the first eval().
  dut->clk_i = 0;
  dut->rst_ni = 0;
  dut->valid_i = 0;
  dut->stall_i = 0;
  dut->inp1_i = 0;
  dut->inp2_i = 0;
  for (int i = 0; i < kRandWords; i++)
    rand_raw[i] = 0;
  dut->eval();
  run_reset(dut, vcd, contextp);

  while (n_checks < kTotStims) {
    dut->clk_i = !dut->clk_i;

    if (dut->clk_i) {
      if (n_stims < kTotStims) {
        const uint32_t a0 = dist(rng) & kShareMask;
        const uint32_t a1 = dist(rng) & kShareMask;
        const uint32_t b0 = dist(rng) & kShareMask;
        const uint32_t b1 = dist(rng) & kShareMask;
        set_share(inp1_raw, 0, a0);
        set_share(inp1_raw, 1, a1);
        set_share(inp2_raw, 0, b0);
        set_share(inp2_raw, 1, b1);
        dut->valid_i = 1;
        for (int i = 0; i < kRandWords; i++)
          rand_raw[i] = dist(rng);

        // Push the golden model result into exp_queue.
        exp_queue.push(((uint64_t)(a0 ^ a1) + (uint64_t)(b0 ^ b1)) &
                       kResultMask);
        n_stims++;
      } else {
        dut->valid_i = 0;
      }
    }

    dut->eval();

    if (dut->clk_i && dut->valid_o && !exp_queue.empty()) {
      const uint64_t s0 = result_share(result_raw, 0);
      const uint64_t s1 = result_share(result_raw, 1);
      const uint64_t got = (s0 ^ s1) & kResultMask;
      const uint64_t exp = exp_queue.front();
      exp_queue.pop();
      n_checks++;
      if (got != exp) {
        n_errs++;
        printf(
            "[FAIL] t=%-8llu | exp=%09llx got=%09llx (s0=%09llx s1=%09llx)\n",
            (unsigned long long)contextp->time(), (unsigned long long)exp,
            (unsigned long long)got, (unsigned long long)s0,
            (unsigned long long)s1);
      }
    }

    vcd->dump(contextp->time());
    contextp->timeInc(1);
  }

  if (n_errs)
    printf("Test ***FAILED*** %d / %d\n", n_errs, n_checks);
  else
    printf("Test ***PASSED*** %d checks\n", n_checks);

  dut->final();
  vcd->close();
  delete vcd;
  delete dut;
  delete contextp;
  return n_errs ? 1 : 0;
}
