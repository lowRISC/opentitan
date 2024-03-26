// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/ibex_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/firmware/sca_lib.h"
#include "sw/device/tests/crypto/cryptotest/firmware/status.h"
#include "sw/device/tests/crypto/cryptotest/json/ibex_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP100 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[8];
static volatile uint32_t sram_main_buffer_batch[256];

/**
 * ibex.sca.tl_write_batch_fvsr_fix_address
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration FvsR values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into a single position in SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write_batch_fvsr_fix_address(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write random data into SRAM at the first address.
    mmio_region_write32(sram_region_main_addr, 0, values[it]);
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_write_batch_fvsr
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration FvsR values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write_batch_fvsr(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write random data into SRAM.
    mmio_region_write32(sram_region_main_addr, it * (ptrdiff_t)sizeof(uint32_t),
                        values[it]);
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_write_batch_random_fix_address
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration random values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into a single position in SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write_batch_random_fix_address(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write random data into SRAM.
    mmio_region_write32(sram_region_main_addr, 0, values[it]);
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_write_batch_random
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration random values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write_batch_random(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write random data into SRAM.
    mmio_region_write32(sram_region_main_addr, it * (ptrdiff_t)sizeof(uint32_t),
                        values[it]);
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_write
 *
 * This SCA penetration test executes the following instructions:
 *  - Set trigger
 *  - Write data over TL-UL into SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  sca_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP100);
  // Write provided data into SRAM.
  for (int i = 0; i < 8; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        uj_data.data[i]);
  }
  sca_set_trigger_low();

  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read_batch_fvsr_fix_address
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration FvsR values using the software LFSR.
 *  - Set trigger
 *  - Read data from a single address in SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read_batch_fvsr_fix_address(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  uint32_t read_data[256];

  // SCA code target.
  // Fetch data from SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    mmio_region_write32(sram_region_main_addr, 0, values[i]);
    asm volatile(NOP100);
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    read_data[i] = mmio_region_read32(sram_region_main_addr, 0);
    sca_set_trigger_low();
  }

  // Write back last value read from SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = read_data[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read_batch_fvsr
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration FvsR values using the software LFSR.
 *  - Set trigger
 *  - Read data from SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read_batch_fvsr(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write provided data into SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        values[i]);
  }

  uint32_t read_data[256];

  // SCA code target.
  // Fetch data from SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    read_data[i] = mmio_region_read32(sram_region_main_addr,
                                      i * (ptrdiff_t)sizeof(uint32_t));
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value read from SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = read_data[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read_batch_random_fix_address
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration random values using the software LFSR.
 *  - Set trigger
 *  - Read data from a single address in SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read_batch_random_fix_address(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  uint32_t read_data[256];
  // SCA code target.
  // Fetch data from SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    mmio_region_write32(sram_region_main_addr, 0, values[i]);
    asm volatile(NOP100);
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    read_data[i] = mmio_region_read32(sram_region_main_addr, 0);
    sca_set_trigger_low();
  }

  // Write back last value read from SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = read_data[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read_batch_random
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration random values using the software LFSR.
 *  - Set trigger
 *  - Read data from SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read_batch_random(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer_batch;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write provided data into SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        values[i]);
  }

  uint32_t read_data[256];

  // SCA code target.

  // Fetch data from SRAM.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    read_data[i] = mmio_region_read32(sram_region_main_addr,
                                      i * (ptrdiff_t)sizeof(uint32_t));
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value read from SRAM to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = read_data[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read
 *
 * This SCA penetration test executes the following instructions:
 *  - Set trigger
 *  - Read data from SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write provided data into SRAM.
  for (int i = 0; i < 8; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        uj_data.data[i]);
  }

  uint32_t read_data[8];

  // SCA code target.
  sca_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP100);
  // Fetch data from SRAM.
  for (int i = 0; i < 8; i++) {
    read_data[i] = mmio_region_read32(sram_region_main_addr,
                                      i * (ptrdiff_t)sizeof(uint32_t));
  }
  sca_set_trigger_low();
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_write_batch_fvsr
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration FvsR values using the software LFSR.
 *  - Set trigger
 *  - Write random data to registers in RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_write_batch_fvsr(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // SCA code target.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write provided data into register file.
    asm volatile("mv x5, %0" : : "r"(values[i]));
    asm volatile("mv x6, %0" : : "r"(values[i]));
    asm volatile("mv x7, %0" : : "r"(values[i]));
    asm volatile("mv x28, %0" : : "r"(values[i]));
    asm volatile("mv x29, %0" : : "r"(values[i]));
    asm volatile("mv x30, %0" : : "r"(values[i]));
    asm volatile("mv x31, %0" : : "r"(values[i]));
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into the RF to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_write_batch_random
 *
 * This SCA penetration test executes the following instructions:
 *  - Generate num_iteration random values using the software LFSR.
 *  - Set trigger
 *  - Write random data to registers in RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_write_batch_random(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  // SCA code target.
  for (int i = 0; i < uj_data.num_iterations; i++) {
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Write provided data into register file.
    asm volatile("mv x5, %0" : : "r"(values[i]));
    asm volatile("mv x6, %0" : : "r"(values[i]));
    asm volatile("mv x7, %0" : : "r"(values[i]));
    asm volatile("mv x28, %0" : : "r"(values[i]));
    asm volatile("mv x29, %0" : : "r"(values[i]));
    asm volatile("mv x30, %0" : : "r"(values[i]));
    asm volatile("mv x31, %0" : : "r"(values[i]));
    sca_set_trigger_low();
    asm volatile(NOP100);
  }

  // Write back last value written into the RF to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_write
 *
 * This SCA penetration test executes the following instructions:
 *  - Set trigger
 *  - Write provided data to registers in RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_write(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // SCA code target.
  sca_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP100);
  // Write provided data into register file.
  asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
  asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
  asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
  asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
  asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
  asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));
  asm volatile("mv x31, %0" : : "r"(uj_data.data[6]));
  sca_set_trigger_low();

  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_read_batch_fvsr
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration FvsR values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_read_batch_fvsr(ujson_t *uj) {
  // Get number of iterations and fixed data.
  ibex_sca_test_fvsr_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_fvsr_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate FvsR values.
  uint32_t values[256];
  bool sample_fixed = true;
  for (int i = 0; i < uj_data.num_iterations; i++) {
    if (sample_fixed) {
      values[i] = uj_data.fixed_data;
    } else {
      values[i] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  for (int i = 0; i < uj_data.num_iterations; i++) {
    // Initialize temporary registers with reference values.
    asm volatile("mv x5, %0" : : "r"(0));
    asm volatile("mv x6, %0" : : "r"(0));
    asm volatile("mv x7, %0" : : "r"(0));
    asm volatile("mv x28, %0" : : "r"(values[i]));
    asm volatile("mv x29, %0" : : "r"(values[i]));
    asm volatile("mv x30, %0" : : "r"(values[i]));
    asm volatile(NOP100);
    // SCA code target.
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Copy registers.
    asm volatile("mv x5, x28");
    asm volatile("mv x6, x29");
    asm volatile("mv x7, x30");
    sca_set_trigger_low();
  }

  // Write back last value written into the RF to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_read_batch_random
 *
 * This SCA penetration test executes the following instructions:
 * - Generate num_iteration random values using the software LFSR.
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_read_batch_random(ujson_t *uj) {
  // Get number of iterations.
  ibex_sca_batch_t uj_data;
  TRY(ujson_deserialize_ibex_sca_batch_t(uj, &uj_data));
  if (uj_data.num_iterations >= 256) {
    LOG_INFO("Error: num_iterations >= 256");
    return ABORTED();
  }

  // Generate random values.
  uint32_t values[256];
  for (int i = 0; i < uj_data.num_iterations; i++) {
    values[i] = prng_rand_uint32();
  }

  for (int i = 0; i < uj_data.num_iterations; i++) {
    // Initialize temporary registers with reference values.
    asm volatile("mv x5, %0" : : "r"(0));
    asm volatile("mv x6, %0" : : "r"(0));
    asm volatile("mv x7, %0" : : "r"(0));
    asm volatile("mv x28, %0" : : "r"(values[i]));
    asm volatile("mv x29, %0" : : "r"(values[i]));
    asm volatile("mv x30, %0" : : "r"(values[i]));
    asm volatile(NOP100);
    // SCA code target.
    sca_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP100);
    // Copy registers.
    asm volatile("mv x5, x28");
    asm volatile("mv x6, x29");
    asm volatile("mv x7, x30");
    sca_set_trigger_low();
  }

  // Write back last value written into the RF to validate generated data.
  ibex_sca_result_t uj_output;
  uj_output.result = values[uj_data.num_iterations - 1];
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_read
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_read(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));
  // Initialize temporary registers with reference values.
  asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
  asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
  asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
  asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
  asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
  asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));

  // SCA code target.
  sca_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP100);
  // Copy registers.
  asm volatile("mv x28, x5");
  asm volatile("mv x29, x6");
  asm volatile("mv x30, x7");
  sca_set_trigger_low();

  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * Initializes the Ibex SCA test.
 *
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_init(ujson_t *uj) {
  // Setup trigger and enable peripherals needed for the test.
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4);

  // Disable the instruction cache and dummy instructions for SCA.
  sca_configure_cpu();

  return OK_STATUS(0);
}

/**
 * Ibex SCA command handler.
 *
 * Command handler for the Ibex SCA command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca(ujson_t *uj) {
  ibex_sca_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexScaSubcommandInit:
      return handle_ibex_sca_init(uj);
    case kIbexScaSubcommandRFRead:
      return handle_ibex_sca_register_file_read(uj);
    case kIbexScaSubcommandRFReadBatchRandom:
      return handle_ibex_sca_register_file_read_batch_random(uj);
    case kIbexScaSubcommandRFReadBatchFvsr:
      return handle_ibex_sca_register_file_read_batch_fvsr(uj);
    case kIbexScaSubcommandRFWrite:
      return handle_ibex_sca_register_file_write(uj);
    case kIbexScaSubcommandRFWriteBatchRandom:
      return handle_ibex_sca_register_file_write_batch_random(uj);
    case kIbexScaSubcommandRFWriteBatchFvsr:
      return handle_ibex_sca_register_file_write_batch_fvsr(uj);
    case kIbexScaSubcommandTLRead:
      return handle_ibex_sca_tl_read(uj);
    case kIbexScaSubcommandTLReadBatchRandom:
      return handle_ibex_sca_tl_read_batch_random(uj);
    case kIbexScaSubcommandTLReadBatchRandomFixAddress:
      return handle_ibex_sca_tl_read_batch_random_fix_address(uj);
    case kIbexScaSubcommandTLReadBatchFvsr:
      return handle_ibex_sca_tl_read_batch_fvsr(uj);
    case kIbexScaSubcommandTLReadBatchFvsrFixAddress:
      return handle_ibex_sca_tl_read_batch_fvsr_fix_address(uj);
    case kIbexScaSubcommandTLWrite:
      return handle_ibex_sca_tl_write(uj);
    case kIbexScaSubcommandTLWriteBatchRandom:
      return handle_ibex_sca_tl_write_batch_random(uj);
    case kIbexScaSubcommandTLWriteBatchRandomFixAddress:
      return handle_ibex_sca_tl_write_batch_random_fix_address(uj);
    case kIbexScaSubcommandTLWriteBatchFvsr:
      return handle_ibex_sca_tl_write_batch_fvsr(uj);
    case kIbexScaSubcommandTLWriteBatchFvsrFixAddress:
      return handle_ibex_sca_tl_write_batch_fvsr_fix_address(uj);
    default:
      LOG_ERROR("Unrecognized IBEX SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
