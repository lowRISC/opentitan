// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstdint>
#include <cstdio>
#include <queue>
#include <random>

#include "Votbn_mask_accelerator.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

static constexpr int kWidth = 32;
static constexpr uint32_t kShareMask = ~0u;

#include "otbn_tb_utils.h"

// mask_op_e encodings from otbn_pkg.sv, paired with display names.
// arith_out: true when result_o carries an arithmetic sharing (s0+s1 mod q),
//            false when it carries a Boolean sharing (s0^s1).
struct Mode {
  uint8_t enc;
  const char *name;
  bool arith_out;
};
static constexpr Mode kModes[] = {
    {0x17, "SecAdd", false},
    {0x0c, "SecAddMod", false},
    {0x0b, "ArithToBool", false},
    {0x10, "BoolToArith", true},
};

static constexpr int kNumModes = sizeof(kModes) / sizeof(kModes[0]);
static constexpr int kVecSize = 8;
static constexpr int kElemPerMode = 1000 * kVecSize;
static constexpr int kRemaskWords = 2;

int main(int argc, char **argv) {
  VerilatedContext *const contextp = new VerilatedContext;
  contextp->commandArgs(argc, argv);
  contextp->traceEverOn(true);

  Votbn_mask_accelerator *const dut =
      new Votbn_mask_accelerator(contextp, "TOP");

  // Access Verilator packed [N:0][W-1:0] ports as flat uint32_t[]
  // (little-endian).
  uint32_t *const rand_raw = reinterpret_cast<uint32_t *>(&dut->rand_i);
  uint32_t *const remask_raw =
      reinterpret_cast<uint32_t *>(&dut->remask_rand_i);
  uint32_t *const result_raw = reinterpret_cast<uint32_t *>(&dut->result_o);
  uint32_t *const in0_raw = reinterpret_cast<uint32_t *>(&dut->in0_i);
  uint32_t *const in1_raw = reinterpret_cast<uint32_t *>(&dut->in1_i);

  // VCD waveform writer receives signal snapshots on each vcd->dump() call.
  VerilatedVcdC *const vcd = new VerilatedVcdC;
  dut->trace(vcd, 99);
  vcd->open("dump.vcd");

  // Mersenne Twister RNG with a fixed seed for deterministic, reproducible
  // timulus.
  std::mt19937 rng(42);
  // Produces uniformly distributed random uint32_t values (full 32-bit range).
  std::uniform_int_distribution<uint32_t> dist;

  // Initialise all inputs to a known state before the first eval().
  dut->clk_i = 0;
  dut->rst_ni = 0;
  dut->sec_wipe_running_i = 0;
  dut->wvalid_i = 0;
  dut->rready_i = 1;
  dut->mask_op_i = kModes[0].enc;
  dut->mod_i = dist(rng) & kShareMask;
  // mod_i = 0 would break rejection sampling
  if (dut->mod_i == 0)
    dut->mod_i = 1;
  for (int i = 0; i < kRandWords; i++)
    rand_raw[i] = 0;
  for (int i = 0; i < kRemaskWords; i++)
    remask_raw[i] = 0;
  set_share(in0_raw, 0, 0);
  set_share(in0_raw, 1, 0);
  set_share(in1_raw, 0, 0);
  set_share(in1_raw, 1, 0);
  dut->eval();

  // Reset the DUT.
  run_reset(dut, vcd, contextp);

  int total_errs = 0;
  const uint32_t mod = dut->mod_i;

  for (int mode = 0; mode < kNumModes; mode++) {
    // Set the operation mode and advance by one cycle.
    dut->mask_op_i = kModes[mode].enc;
    tick(dut, vcd, contextp);

    int n_stims = 0, n_checks = 0, n_errs = 0;

    // FIFO of expected kWidth-bit results. Each entry is pushed when a stimulus
    // is accepted (wvalid_i && wready_o) and popped when rvalid_o fires.
    std::queue<uint32_t> exp_queue;

    // Stimulus and result-check loop.
    while (n_checks < kElemPerMode) {
      // Drive fresh randomness before the rising edge.
      // For BoolToArith, wready_o is combinational on remask_rand_i[0].
      for (int i = 0; i < kRandWords; i++)
        rand_raw[i] = dist(rng);
      for (int i = 0; i < kRemaskWords; i++)
        remask_raw[i] = dist(rng) & kShareMask;

      uint32_t golden = 0;
      if (n_stims < kElemPerMode) {
        uint32_t a0, a1, b0 = 0, b1 = 0;
        if (mode == 1) {  // SecAddMod
          const uint32_t inp1 = dist(rng) % mod;
          const uint32_t inp2 = dist(rng) % mod;
          const uint32_t ma = dist(rng) & kShareMask;
          const uint32_t mb = dist(rng) & kShareMask;
          a0 = (inp1 - mod) ^ ma;
          a1 = ma;
          b0 = inp2 ^ mb;
          b1 = mb;
          golden = (uint32_t)(((uint64_t)inp1 + inp2) % mod);
        } else if (mode == 2) {  // ArithToBool
          const uint32_t inp1 = dist(rng) % mod;
          const uint32_t inp2 = dist(rng) % mod;
          a0 = inp1;
          a1 = inp2;
          golden = (uint32_t)(((uint64_t)inp1 + inp2) % mod);
        } else if (mode == 3) {  // BoolToArith
          const uint32_t secret = dist(rng) % mod;
          const uint32_t ma = dist(rng) & kShareMask;
          a0 = secret ^ ma;
          a1 = ma;
          golden = secret;
        } else {  // SecAdd
          a0 = dist(rng) & kShareMask;
          a1 = dist(rng) & kShareMask;
          b0 = dist(rng) & kShareMask;
          b1 = dist(rng) & kShareMask;
          golden = ((a0 ^ a1) + (b0 ^ b1)) & kShareMask;
        }
        set_share(in0_raw, 0, a0);
        set_share(in0_raw, 1, a1);
        set_share(in1_raw, 0, b0);
        set_share(in1_raw, 1, b1);
        dut->wvalid_i = 1;
      } else {
        dut->wvalid_i = 0;
      }

      // Settle combinational outputs after driving fresh randomness so that
      // wready_o reflects the current remask_rand_i before we sample it.
      // For BoolToArith, wready_o is gated by (mask_mod < mod_i) which is
      // purely combinational on remask_rand_i[0], without this eval() the
      // acceptance decision would be one cycle stale.
      dut->eval();
      const bool accepted = dut->wvalid_i && dut->wready_o;

      // Rising edge
      dut->clk_i = 1;
      dut->eval();

      if (accepted) {
        exp_queue.push(golden);
        n_stims++;
      }

      if (dut->rvalid_o && !exp_queue.empty()) {
        const uint32_t s0 = get_share(result_raw, 0);
        const uint32_t s1 = get_share(result_raw, 1);
        const uint32_t got = kModes[mode].arith_out
                                 ? (uint32_t)(((uint64_t)s0 + s1) % mod)
                                 : (s0 ^ s1) & kShareMask;
        const uint32_t exp = exp_queue.front();
        exp_queue.pop();
        n_checks++;
        if (got != exp) {
          n_errs++;
          printf(
              "[FAIL] mode=%d t=%-8llu | exp=%08x got=%08x (s0=%08x s1=%08x)\n",
              mode, (unsigned long long)contextp->time(), exp, got, s0, s1);
        }
      }

      vcd->dump(contextp->time());
      contextp->timeInc(1);

      // Falling edge
      dut->clk_i = 0;
      dut->eval();
      vcd->dump(contextp->time());
      contextp->timeInc(1);
    }

    printf("Mode %d (%s): %s - %d errors / %d checks\n", mode,
           kModes[mode].name, n_errs ? "FAIL" : "PASS", n_errs, n_checks);
    total_errs += n_errs;
  }

  if (total_errs)
    printf("Test ***FAILED*** %d total errors\n", total_errs);
  else
    printf("Test ***PASSED*** all 4 modes\n");

  dut->final();
  vcd->close();
  delete vcd;
  delete dut;
  delete contextp;
  return total_errs ? 1 : 0;
}
