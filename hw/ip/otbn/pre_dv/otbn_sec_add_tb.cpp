// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstdint>
#include <cstdio>
#include <queue>
#include <random>
#include <type_traits>

#include "Votbn_sec_add.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

// Width of each adder input in bits.
// This tesbench has only been run with Width as 4, 8, 16 or 32.
// Override at compile time with -DWIDTH=<n> (e.g. -DWIDTH=16).
#ifndef WIDTH
#define WIDTH 32
#endif

static constexpr int kWidth = WIDTH;
static_assert(kWidth >= 4 && kWidth <= 32,
              "Testbench only supports 4 <= Width <= 32.");

// constexpr floor-log2, which equals $clog2 for power-of-2 values.
constexpr int clog2(int n) { return n <= 1 ? 0 : 1 + clog2(n >> 1); }

static constexpr int kStages = clog2(kWidth);
static constexpr int kRandWidth = 2 * (kStages * kWidth + 1);
static constexpr int kRandWords = (kRandWidth + 31) / 32;

// Mask for a single (kWidth+1)-bit result share.
static constexpr uint64_t kResultMask = (2ULL << kWidth) - 1;

// Mask to restrict random stimulus values to kWidth bits.
static constexpr uint32_t kShareMask =
    (kWidth == 32) ? ~0u : ((1u << kWidth) - 1);

static constexpr int TOT_STIMS = 1'000'000;
static constexpr int RST_HALF_CLK = 20;  // 10 full clock cycles

// Extract one (kWidth+1)-bit share from result_o[1:0][kWidth:0] viewed as
// uint32_t[].
static uint64_t result_share(const uint32_t *r, int share) {
  const int lo_word = (share * (kWidth + 1)) / 32;
  const int lo_shift = (share * (kWidth + 1)) % 32;
  uint64_t bits = (uint64_t)r[lo_word];
  // Only read the next word if the share spans a 32-bit boundary.
  if (lo_shift + kWidth + 1 > 32)
    bits |= (uint64_t)r[lo_word + 1] << 32;
  return (bits >> lo_shift) & kResultMask;
}

int main(int argc, char **argv) {
  VerilatedContext *const contextp = new VerilatedContext;
  contextp->commandArgs(argc, argv);
  contextp->traceEverOn(true);

  Votbn_sec_add *const dut = new Votbn_sec_add(contextp, "TOP");
  // rand_i is IData/QData/WData depending on kRandWidth; access it as
  // uint32_t[] regardless of Verilator type, safe on little-endian hosts for
  // kWidth >= 4.
  uint32_t *const rand_raw = reinterpret_cast<uint32_t *>(&dut->rand_i);
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

  // Propagate initial input values through all combinational logic.
  dut->eval();

  while (n_checks < TOT_STIMS) {
    dut->clk_i = !dut->clk_i;

    // Release reset after 10 cycles.
    if (contextp->time() == RST_HALF_CLK)
      dut->rst_ni = 1;

    if (dut->clk_i && dut->rst_ni) {
      // Drive stimulus and push golden value for what the DUT will capture this
      // edge.
      if (n_stims < TOT_STIMS) {
        // a0/a1: shares 0 and 1 of inp1_i.
        const uint32_t a0 = dist(rng) & kShareMask;
        const uint32_t a1 = dist(rng) & kShareMask;
        // b0/b1: shares 0 and 1 of inp2_i.
        const uint32_t b0 = dist(rng) & kShareMask;
        const uint32_t b1 = dist(rng) & kShareMask;
        // Verilator packs [1:0][kWidth-1:0] as a flat 2*kWidth-bit integer:
        // share1 in the upper half, share0 in the lower half. Cast to the
        // port's exact Verilator type to suppress narrowing warnings (QData for
        // kWidth=32, IData for 16, SData for 8).
        dut->inp1_i =
            static_cast<std::remove_reference_t<decltype(dut->inp1_i)>>(
                ((uint64_t)a1 << kWidth) | a0);
        dut->inp2_i =
            static_cast<std::remove_reference_t<decltype(dut->inp2_i)>>(
                ((uint64_t)b1 << kWidth) | b0);
        dut->valid_i = 1;
        for (int i = 0; i < kRandWords; i++)
          rand_raw[i] = dist(rng);

        // Push the golden model computation of the result into exp_queue.
        exp_queue.push(((uint64_t)(a0 ^ a1) + (uint64_t)(b0 ^ b1)) &
                       kResultMask);

        n_stims++;
      } else {
        dut->valid_i = 0;
      }
    }

    // Propagate the clock edge and any driven inputs through the DUT.
    dut->eval();

    // Compare the DUT output to the golden model.
    if (dut->clk_i && dut->rst_ni && dut->valid_o && !exp_queue.empty()) {
      const uint32_t *res = reinterpret_cast<const uint32_t *>(&dut->result_o);
      const uint64_t s0 = result_share(res, 0);
      const uint64_t s1 = result_share(res, 1);
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

    // Record all signal values at the current time step into the VCD file.
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
