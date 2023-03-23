// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rand_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * The polynomial co-efficients used in the 32-bit LFSR implementation.
 *
 * This implementation matches the RTL design at `hw/ip/prim/rtl/prim_lfsr.sv`.
 */
static const uint32_t kLfsrPolynomialCoefficients = 0x80000057;

/**
 * The default timeout in usecs for fetching data from the entropy source.
 */
static const uint32_t kEntropyFetchTimeoutMicros = 100000;

rand_testutils_rng_t rand_testutils_init(dif_rv_core_ibex_t *rv_core_ibex) {
  CHECK(rv_core_ibex != NULL);
  // For the simulation platforms (DV and Verilator), the LFSR reseed frequency
  // is arbitrarily set to 255. The test may choose to update this value if
  // needed.
  rand_testutils_rng_t ctx = (rand_testutils_rng_t){
      .rv_core_ibex = rv_core_ibex,
      .entropy_fetch_timeout_usec = kEntropyFetchTimeoutMicros,
      .lfsr = 0xdeadbeef,  // Arbitrary.
      .polynomial_coefficients = kLfsrPolynomialCoefficients,
      .reseed_frequency = 256,
      .op_counter = UINT32_MAX};
  // For non-runtime-sensitive simulations (for example, using FPGA or the
  // debug board), always fetch random data from the hardware.
  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    ctx.reseed_frequency = 0;
  }
  return ctx;
}

static inline void reseed_lfsr(void) {
  CHECK_STATUS_OK(rv_core_ibex_testutils_get_rnd_data(
      rand_testutils_rng_ctx.rv_core_ibex,
      rand_testutils_rng_ctx.entropy_fetch_timeout_usec,
      &rand_testutils_rng_ctx.lfsr));
  rand_testutils_rng_ctx.op_counter = 0;
}

static inline void advance_lfsr(void) {
  bool lsb = rand_testutils_rng_ctx.lfsr & 0x1u;
  rand_testutils_rng_ctx.lfsr >>= 1;
  if (lsb) {
    rand_testutils_rng_ctx.lfsr ^=
        rand_testutils_rng_ctx.polynomial_coefficients;
  }
  rand_testutils_rng_ctx.op_counter++;
}

extern void rand_testutils_reseed(void);

uint32_t rand_testutils_gen32(void) {
  if (rand_testutils_rng_ctx.op_counter >=
      rand_testutils_rng_ctx.reseed_frequency) {
    reseed_lfsr();
  } else {
    advance_lfsr();
  }
  return rand_testutils_rng_ctx.lfsr;
}

uint32_t rand_testutils_gen32_range(uint32_t min, uint32_t max) {
  CHECK(max >= min);
  uint32_t range = max - min;
  if (range == 0) {
    return min;
  }
  uint32_t result = min + (rand_testutils_gen32() % (range + 1));
  CHECK(result >= min && result <= max);
  return result;
}

void rand_testutils_shuffle(void *array, size_t size, size_t length) {
  if (length <= 1) {
    return;
  }
  unsigned char temp[size];
  unsigned char *array8 = array;
  uint32_t reseed_frequency = rand_testutils_rng_ctx.reseed_frequency;
  rand_testutils_rng_ctx.reseed_frequency = UINT32_MAX;
  for (size_t i = length - 2; i > 0; i--) {
    size_t j = rand_testutils_gen32_range(0, i + 1);
    memcpy(temp, array8 + j * size, size);
    memcpy(array8 + j * size, array8 + i * size, size);
    memcpy(array8 + i * size, temp, size);
  }
  rand_testutils_rng_ctx.reseed_frequency = reseed_frequency;
}
