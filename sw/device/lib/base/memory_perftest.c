// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  kBufLen = 1000,
  kNumRuns = 10,
};

typedef struct perf_test {
  // A human-readable name for this particular test, e.g. "memcpy".
  const char *label;

  // Setup functions for each context buffer. These function pointers must not
  // be NULL. The runtime of these functions will not be measured.
  void (*setup_buf1)(uint8_t *, size_t);
  void (*setup_buf2)(uint8_t *, size_t);

  // A function that exercises the function under test, e.g. memcpy. This
  // function pointer must not be NULL. The runtime of this function will be
  // measured.
  void (*func)(uint8_t *buf1, uint8_t *buf2, size_t num_runs);

  // The expected number of CPU cycles that `func` will take to run.
  size_t expected_num_cycles;
} perf_test_t;

// Run the given `perf_test_t` and return the number of cycles it took.
static inline uint64_t perf_test_run(const perf_test_t *test, uint8_t *buf1,
                                     uint8_t *buf2, size_t num_runs) {
  CHECK(test->setup_buf1 != NULL);
  CHECK(test->setup_buf2 != NULL);
  CHECK(test->func != NULL);

  uint64_t total_clock_cycles = 0;
  for (size_t i = 0; i < num_runs; ++i) {
    test->setup_buf1(buf1, kBufLen);
    test->setup_buf2(buf2, kBufLen);

    uint64_t start_cycles = ibex_mcycle_read();
    test->func(buf1, buf2, kBufLen);
    uint64_t end_cycles = ibex_mcycle_read();

    // Even if the 64-bit cycle counter overflowed while running the test, the
    // following subtraction would still be well-defined and correct, provided
    // that the test ran in fewer than 2**64 cycles. Practically, we should
    // never see it overflow. Even if it took 12 hours to run all the perf
    // tests, the clock would have to run at 427 THz to overflow the counter
    // (2**64 cycles / (12 * 60 * 60) seconds).
    const uint64_t num_cycles = end_cycles - start_cycles;

    CHECK(total_clock_cycles < UINT64_MAX - num_cycles);
    total_clock_cycles += num_cycles;
  }

  return total_clock_cycles;
}

// Fill the buffer with arbitrary, but deterministically-selected bytes.
static inline void fill_buf_deterministic_values(uint8_t *buf, size_t len) {
  uint32_t state = 42;
  for (size_t i = 0; i < len; ++i) {
    state = state * 17 + i;
    buf[i] = (uint8_t)state;
  }
}

// Zero out the buffer.
static inline void fill_buf_zeroes(uint8_t *buf, size_t len) {
  memset(buf, 0, len);
}

// Zero out the buffer, but put a one at the end.
static inline void fill_buf_zeroes_then_one(uint8_t *buf, size_t len) {
  fill_buf_zeroes(buf, len);
  buf[len - 1] = 1;
}

// Zero out the buffer, but put a one at the beginning.
static inline void fill_buf_one_then_zeroes(uint8_t *buf, size_t len) {
  fill_buf_zeroes(buf, len);
  buf[0] = 1;
}

OT_NOINLINE void test_memcpy(uint8_t *buf1, uint8_t *buf2, size_t len) {
  memcpy(buf1, buf2, len);
}

OT_NOINLINE void test_memset(uint8_t *buf1, uint8_t *buf2, size_t len) {
  const int value = buf2[0];
  memset(buf1, value, len);
}

OT_NOINLINE void test_memcmp(uint8_t *buf1, uint8_t *buf2, size_t len) {
  memcmp(buf1, buf2, len);
}

OT_NOINLINE void test_memrcmp(uint8_t *buf1, uint8_t *buf2, size_t len) {
  memrcmp(buf1, buf2, len);
}

OT_NOINLINE void test_memchr(uint8_t *buf1, uint8_t *buf2, size_t len) {
  const uint8_t value = buf1[len - 1];
  memchr(buf1, value, len);
}

OT_NOINLINE void test_memrchr(uint8_t *buf1, uint8_t *buf2, size_t len) {
  const uint8_t value = buf1[0];
  memrchr(buf1, value, len);
}

OTTF_DEFINE_TEST_CONFIG();

// Each value of `expected_num_cycles` was determined experimentally by
// testing on a CW310 FPGA with the following command:
//
//   $ ./bazelisk.sh test --copt -O2 --test_output=all \
//       //sw/device/lib/base:memory_perftest_fpga_cw310
//
// There are a handful of reasons why the expected number of cycles for this
// test might be inaccurate. Here are a few of them:
//
//   (1) You've changed the definition of the test, e.g. changing the size of
//       the test buffers.
//   (2) You've changed the implementation of memset, memcpy, etc. and they can
//       do the same job in fewer cycles.
//   (3) The test was not compiled with `-O2`. The hardcoded cycle count
//       expectations assume `-O2`.
//   (4) The compiler has gotten smarter.
//   (5) The icache gets turned on prior to test execution.
//
// If you observe the cycle count is smaller the hardcoded expectation, that's
// probably a good thing; please update the expectation!
static const perf_test_t kPerfTests[] = {
    {
        .label = "memcpy",
        .setup_buf1 = &fill_buf_deterministic_values,
        .setup_buf2 = &fill_buf_deterministic_values,
        .func = &test_memcpy,
        .expected_num_cycles = 33270,
    },
    {
        .label = "memcpy_zeroes",
        .setup_buf1 = &fill_buf_deterministic_values,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memcpy,
        .expected_num_cycles = 33270,
    },
    {
        .label = "memset",
        .setup_buf1 = &fill_buf_zeroes,
        .setup_buf2 = &fill_buf_deterministic_values,
        .func = &test_memset,
        .expected_num_cycles = 23200,
    },
    {
        .label = "memset_zeroes",
        .setup_buf1 = &fill_buf_zeroes,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memset,
        .expected_num_cycles = 23200,
    },
    {
        .label = "memcmp_pathological",
        .setup_buf1 = &fill_buf_zeroes_then_one,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memcmp,
        .expected_num_cycles = 110740,
    },
    {
        .label = "memcmp_zeroes",
        .setup_buf1 = &fill_buf_zeroes,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memcmp,
        .expected_num_cycles = 110740,
    },
    {
        .label = "memrcmp_pathological",
        .setup_buf1 = &fill_buf_zeroes,
        .setup_buf2 = &fill_buf_one_then_zeroes,
        .func = &test_memrcmp,
        .expected_num_cycles = 50740,
    },
    {
        .label = "memrcmp_zeroes",
        .setup_buf1 = &fill_buf_zeroes,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memrcmp,
        .expected_num_cycles = 50850,
    },
    {
        .label = "memchr_pathological",
        .setup_buf1 = &fill_buf_deterministic_values,
        .setup_buf2 = &fill_buf_zeroes,
        .func = &test_memchr,
        .expected_num_cycles = 7250,
    },
    {
        .label = "memrchr_pathological",
        .setup_buf1 = &fill_buf_deterministic_values,
        .setup_buf2 = &fill_buf_deterministic_values,
        .func = &test_memrchr,
        .expected_num_cycles = 23850,
    },
};

static uint8_t buf1[kBufLen];
static uint8_t buf2[kBufLen];

bool test_main(void) {
  bool all_expectations_match = true;
  for (size_t i = 0; i < ARRAYSIZE(kPerfTests); ++i) {
    const perf_test_t *test = &kPerfTests[i];

    const uint64_t num_cycles = perf_test_run(test, buf1, buf2, kNumRuns);
    if (num_cycles != test->expected_num_cycles) {
      all_expectations_match = false;
      // Cast cycle counts to `uint32_t` before printing because `base_printf()`
      // cannot print `uint64_t`.
      CHECK(test->expected_num_cycles < UINT32_MAX);
      CHECK(num_cycles < UINT32_MAX);
      const uint32_t expected_num_cycles_u32 =
          (uint32_t)test->expected_num_cycles;
      const uint32_t num_cycles_u32 = (uint32_t)num_cycles;

      CHECK(num_cycles < UINT32_MAX / 100);
      const uint32_t percent_change =
          (100 * num_cycles_u32) / expected_num_cycles_u32;

      LOG_WARNING(
          "%s:\n"
          "  Expected:        %10d cycles\n"
          "  Actual:          %10d cycles\n"
          "  Actual/Expected: %10d%%\n",
          test->label, expected_num_cycles_u32, num_cycles_u32, percent_change);
    }
  }
  return all_expectations_match;
}
