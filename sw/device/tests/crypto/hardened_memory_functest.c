// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "rv_core_ibex_regs.h"

#define MULTI_WORD_TEST_SIZE 4

__attribute__((noinline)) static uint32_t run_xor_test(uint32_t a_val,
                                                       uint32_t b_val,
                                                       uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t b[] = {b_val};

  uint64_t start_cycles = profile_start();
  hardened_xor(a, b, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_add_test(uint32_t a_val,
                                                       uint32_t b_val,
                                                       uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t b[] = {b_val};

  uint64_t start_cycles = profile_start();
  hardened_add(a, b, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_sub_test(uint32_t a_val,
                                                       uint32_t b_val,
                                                       uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t b[] = {b_val};

  uint64_t start_cycles = profile_start();
  hardened_sub(a, b, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_add_mod_test(uint32_t a_val,
                                                           uint32_t b_val,
                                                           uint32_t n_val,
                                                           uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t b[] = {b_val};
  uint32_t n[] = {n_val};

  uint64_t start_cycles = profile_start();
  hardened_add_mod(a, b, n, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_sub_mod_test(uint32_t a_val,
                                                           uint32_t b_val,
                                                           uint32_t n_val,
                                                           uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t b[] = {b_val};
  uint32_t n[] = {n_val};

  uint64_t start_cycles = profile_start();
  hardened_sub_mod(a, b, n, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_mod_test(uint32_t a_val,
                                                       uint32_t n_val,
                                                       uint32_t *res) {
  uint32_t a[] = {a_val};
  uint32_t n[] = {n_val};

  uint64_t start_cycles = profile_start();
  hardened_mod_reduce(a, n, 1, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_xor_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *b_val,
    uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t b[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    b[i] = b_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_xor(a, b, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_add_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *b_val,
    uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t b[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    b[i] = b_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_add(a, b, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_sub_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *b_val,
    uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t b[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    b[i] = b_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_sub(a, b, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_add_mod_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *b_val,
    volatile const uint32_t *n_val, uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t b[MULTI_WORD_TEST_SIZE];
  uint32_t n[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    b[i] = b_val[i];
    n[i] = n_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_add_mod(a, b, n, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_sub_mod_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *b_val,
    volatile const uint32_t *n_val, uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t b[MULTI_WORD_TEST_SIZE];
  uint32_t n[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    b[i] = b_val[i];
    n[i] = n_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_sub_mod(a, b, n, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

__attribute__((noinline)) static uint32_t run_mod_reduce_test_multi(
    volatile const uint32_t *a_val, volatile const uint32_t *n_val,
    uint32_t *res) {
  uint32_t a[MULTI_WORD_TEST_SIZE];
  uint32_t n[MULTI_WORD_TEST_SIZE];
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    a[i] = a_val[i];
    n[i] = n_val[i];
  }

  uint64_t start_cycles = profile_start();
  hardened_mod_reduce(a, n, MULTI_WORD_TEST_SIZE, res);
  uint32_t cycles = profile_end(start_cycles);

  return cycles;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  uint32_t cycles_1, cycles_2;
  uint32_t res_1[1], res_2[1], res_3[1];

  // For the timing test, we disable the instruction cache.
  hardened_bool_t icache_enabled;
  CHECK_STATUS_OK(ibex_disable_icache(&icache_enabled));
  // We enable data independent timing.
  CSR_SET_BITS(CSR_REG_CPUCTRL, 0x1 << 0x1);
  // We disable dummy instructions.
  CSR_CLEAR_BITS(CSR_REG_CPUCTRL, 0x1 << 0x2);

  LOG_INFO("Testing hardened_xor");
  volatile uint32_t xor_a1 = 0x1;
  volatile uint32_t xor_b1 = 0x1;
  volatile uint32_t xor_a2 = 0xFF;
  volatile uint32_t xor_b2 = 0xFF;
  cycles_1 = run_xor_test(xor_a1, xor_b1, res_1);
  cycles_2 = run_xor_test(xor_a2, xor_b2, res_2);
  CHECK(cycles_1 == cycles_2, "hardened_xor is not constant-time");
  CHECK(res_1[0] == 0x0, "hardened_xor correctness failed (1^1)");
  CHECK(res_2[0] == 0x0, "hardened_xor correctness failed (FF^FF)");

  LOG_INFO("Testing hardened_add");
  volatile uint32_t add_a1 = 0x1;
  volatile uint32_t add_b1 = 0x1;
  volatile uint32_t add_a2 = 0xFF;
  volatile uint32_t add_b2 = 0xFF;
  cycles_1 = run_add_test(add_a1, add_b1, res_1);
  cycles_2 = run_add_test(add_a2, add_b2, res_2);
  CHECK(cycles_1 == cycles_2, "hardened_add is not constant-time");
  CHECK(res_1[0] == 0x2, "hardened_add correctness failed (1+1)");
  CHECK(res_2[0] == 0x1FE, "hardened_add correctness failed (FF+FF)");

  LOG_INFO("Testing hardened_sub");
  volatile uint32_t sub_a1 = 0x1;
  volatile uint32_t sub_b1 = 0x1;
  volatile uint32_t sub_a2 = 0xFF;
  volatile uint32_t sub_b2 = 0x1;
  cycles_1 = run_sub_test(sub_a1, sub_b1, res_1);
  cycles_2 = run_sub_test(sub_a2, sub_b2, res_2);
  CHECK(cycles_1 == cycles_2, "hardened_sub is not constant-time");
  CHECK(res_1[0] == 0x0, "hardened_sub correctness failed (1-1)");
  CHECK(res_2[0] == 0xFE, "hardened_sub correctness failed (FF-1)");

  LOG_INFO("Testing hardened_add_mod");
  volatile uint32_t add_mod_a1 = 0x1;
  volatile uint32_t add_mod_b1 = 0x1;
  volatile uint32_t add_mod_n1 = 0x100;
  volatile uint32_t add_mod_a2 = 0xFF;
  volatile uint32_t add_mod_b2 = 0xFF;
  volatile uint32_t add_mod_n2 = 0x100;
  cycles_1 = run_add_mod_test(add_mod_a1, add_mod_b1, add_mod_n1, res_1);
  cycles_2 = run_add_mod_test(add_mod_a2, add_mod_b2, add_mod_n2, res_2);
  CHECK(cycles_1 == cycles_2, "hardened_add_mod is not constant-time");
  CHECK(res_1[0] == 0x2, "hardened_add_mod correctness failed: value < n");
  CHECK(res_2[0] == 0xFE,
        "hardened_add_mod correctness failed: value >= n (0x1FE mod 0x100)");

  LOG_INFO("Testing hardened_sub_mod");
  volatile uint32_t sub_mod_a1 = 0x1;
  volatile uint32_t sub_mod_b1 = 0x1;
  volatile uint32_t sub_mod_n1 = 0x100;
  volatile uint32_t sub_mod_a2 = 0xFF;
  volatile uint32_t sub_mod_b2 = 0x1;
  volatile uint32_t sub_mod_n2 = 0x100;
  // Extra case to test borrow correctness: a < b
  volatile uint32_t sub_mod_a3 = 0x1;
  volatile uint32_t sub_mod_b3 = 0x5;
  volatile uint32_t sub_mod_n3 = 0x100;

  cycles_1 = run_sub_mod_test(sub_mod_a1, sub_mod_b1, sub_mod_n1, res_1);
  cycles_2 = run_sub_mod_test(sub_mod_a2, sub_mod_b2, sub_mod_n2, res_2);
  run_sub_mod_test(sub_mod_a3, sub_mod_b3, sub_mod_n3, res_3);
  CHECK(cycles_1 == cycles_2, "hardened_sub_mod is not constant-time");
  CHECK(res_1[0] == 0x0, "hardened_sub_mod correctness failed: a == b");
  CHECK(res_2[0] == 0xFE, "hardened_sub_mod correctness failed: a > b");
  CHECK(res_3[0] == 0xFC, "hardened_sub_mod correctness failed: a < b");

  LOG_INFO("Testing hardened_mod_reduce");
  uint32_t mod_a1 = 0x1;
  uint32_t mod_n1 = 0x100;
  uint32_t mod_a2 = 0xFF;
  uint32_t mod_n2 = 0x100;
  cycles_1 = run_mod_test(mod_a1, mod_n1, res_1);
  cycles_2 = run_mod_test(mod_a2, mod_n2, res_2);
  CHECK(cycles_1 == cycles_2, "hardened_mod_reduce is not constant-time");
  CHECK(res_1[0] == 0x1, "hardened_mod_reduce correctness failed (1 mod 100)");
  CHECK(res_2[0] == 0xFF,
        "hardened_mod_reduce correctness failed (FF mod 100)");

  LOG_INFO("Starting multi-word tests");
  uint32_t res_multi_1[MULTI_WORD_TEST_SIZE];
  uint32_t res_multi_2[MULTI_WORD_TEST_SIZE];
  uint32_t res_multi_3[MULTI_WORD_TEST_SIZE];

  LOG_INFO("Testing hardened_xor (multi-word)");
  volatile uint32_t xor_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t xor_b1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t xor_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t xor_b2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    xor_a1_multi[i] = 0x1;
    xor_b1_multi[i] = 0x1;
    xor_a2_multi[i] = 0xFFFFFFFF;
    xor_b2_multi[i] = 0xFFFFFFFF;
  }
  cycles_1 = run_xor_test_multi(xor_a1_multi, xor_b1_multi, res_multi_1);
  cycles_2 = run_xor_test_multi(xor_a2_multi, xor_b2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2, "hardened_xor (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x0, "hardened_xor multi correctness failed");

  LOG_INFO("Testing hardened_add (multi-word)");
  volatile uint32_t add_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_b1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_b2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    add_a1_multi[i] = 0x1;
    add_b1_multi[i] = 0x1;
    add_a2_multi[i] = 0xFFFFFFFF;
    add_b2_multi[i] = 0xFFFFFFFF;
  }
  cycles_1 = run_add_test_multi(add_a1_multi, add_b1_multi, res_multi_1);
  cycles_2 = run_add_test_multi(add_a2_multi, add_b2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2, "hardened_add (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x2, "hardened_add multi correctness failed");

  LOG_INFO("Testing hardened_sub (multi-word)");
  volatile uint32_t sub_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_b1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_b2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    sub_a1_multi[i] = 0x1;
    sub_b1_multi[i] = 0x1;
    sub_a2_multi[i] = 0xFFFFFFFF;
    sub_b2_multi[i] = 0x1;
  }
  cycles_1 = run_sub_test_multi(sub_a1_multi, sub_b1_multi, res_multi_1);
  cycles_2 = run_sub_test_multi(sub_a2_multi, sub_b2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2, "hardened_sub (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x0, "hardened_sub multi correctness failed");

  LOG_INFO("Testing hardened_add_mod (multi-word)");
  volatile uint32_t add_mod_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_mod_b1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_mod_n1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_mod_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_mod_b2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t add_mod_n2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    add_mod_a1_multi[i] = 0x1;
    add_mod_b1_multi[i] = 0x1;
    add_mod_n1_multi[i] = 0x100;
    add_mod_a2_multi[i] = 0xFFFFFFFF;
    add_mod_b2_multi[i] = 0xFFFFFFFF;
    add_mod_n2_multi[i] = 0x100;
  }
  cycles_1 = run_add_mod_test_multi(add_mod_a1_multi, add_mod_b1_multi,
                                    add_mod_n1_multi, res_multi_1);
  cycles_2 = run_add_mod_test_multi(add_mod_a2_multi, add_mod_b2_multi,
                                    add_mod_n2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2,
        "hardened_add_mod (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x2, "hardened_add_mod multi correctness failed");

  volatile uint32_t am_a3[MULTI_WORD_TEST_SIZE] = {8, 0, 0, 0};
  volatile uint32_t am_b3[MULTI_WORD_TEST_SIZE] = {4, 0, 0, 0};
  volatile uint32_t am_n3[MULTI_WORD_TEST_SIZE] = {10, 0, 0, 0};
  run_add_mod_test_multi(am_a3, am_b3, am_n3, res_multi_3);
  CHECK(res_multi_3[0] == 0x2 && res_multi_3[1] == 0,
        "hardened_add_mod multi branch-select failed");

  LOG_INFO("Testing hardened_sub_mod (multi-word)");
  volatile uint32_t sub_mod_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_mod_b1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_mod_n1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_mod_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_mod_b2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t sub_mod_n2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    sub_mod_a1_multi[i] = 0x1;
    sub_mod_b1_multi[i] = 0x1;
    sub_mod_n1_multi[i] = 0x100;
    sub_mod_a2_multi[i] = 0xFFFFFFFF;
    sub_mod_b2_multi[i] = 0x1;
    sub_mod_n2_multi[i] = 0x100;
  }
  cycles_1 = run_sub_mod_test_multi(sub_mod_a1_multi, sub_mod_b1_multi,
                                    sub_mod_n1_multi, res_multi_1);
  cycles_2 = run_sub_mod_test_multi(sub_mod_a2_multi, sub_mod_b2_multi,
                                    sub_mod_n2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2,
        "hardened_sub_mod (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x0, "hardened_sub_mod multi correctness failed");

  volatile uint32_t sm_a3[MULTI_WORD_TEST_SIZE] = {2, 0, 0, 0};
  volatile uint32_t sm_b3[MULTI_WORD_TEST_SIZE] = {5, 0, 0, 0};
  volatile uint32_t sm_n3[MULTI_WORD_TEST_SIZE] = {10, 0, 0, 0};
  run_sub_mod_test_multi(sm_a3, sm_b3, sm_n3, res_multi_3);
  CHECK(res_multi_3[0] == 0x7 && res_multi_3[1] == 0,
        "hardened_sub_mod multi branch-select failed");

  LOG_INFO("Testing hardened_mod_reduce (multi-word)");
  volatile uint32_t mod_a1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t mod_n1_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t mod_a2_multi[MULTI_WORD_TEST_SIZE] = {0};
  volatile uint32_t mod_n2_multi[MULTI_WORD_TEST_SIZE] = {0};
  for (size_t i = 0; i < MULTI_WORD_TEST_SIZE; ++i) {
    mod_a1_multi[i] = 0x1;
    mod_n1_multi[i] = 0x100;
    mod_a2_multi[i] = 0xFFFFFFFF;
    mod_n2_multi[i] = 0x100;
  }
  cycles_1 = run_mod_reduce_test_multi(mod_a1_multi, mod_n1_multi, res_multi_1);
  cycles_2 = run_mod_reduce_test_multi(mod_a2_multi, mod_n2_multi, res_multi_2);
  CHECK(cycles_1 == cycles_2,
        "hardened_mod_reduce (multi-word) is not constant-time");
  CHECK(res_multi_1[0] == 0x1, "hardened_mod_reduce multi correctness failed");

  return true;
}
