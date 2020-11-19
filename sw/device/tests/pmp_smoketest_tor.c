// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/pmp.h"

#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

/**
 * PMP regions that are used for load/store and execution permission violation
 * tests.
 *
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Address Matching":
 *
 * "If PMP entry i’s A field is set to TOR, the entry matches any address y
 * such that pmpaddri−1 <= y < pmpaddri. If PMP entry 0’s A field is set to TOR,
 * zero is used for the lower bound, and so it matches any address
 * y < pmpaddr0."
 *
 * To prtotect an address range that starts above 0 address, the first region
 * we can use is 1.
 */
#define PMP_LOAD_REGION_ID 2

#define PMP_LOAD_RANGE_BUFFER_SIZE 2048
#define PMP_LOAD_RANGE_SIZE 1024
#define PMP_LOAD_RANGE_BOTTOM_OFFSET 0
#define PMP_LOAD_RANGE_TOP_OFFSET 1023

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool pmp_load_exception;

/**
 * The buffer that is used for load/store access violation test.
 */
__attribute__((aligned(PMP_LOAD_RANGE_SIZE)))  //
static volatile char pmp_load_test_data[PMP_LOAD_RANGE_BUFFER_SIZE];

static uint32_t get_mepc(void) {
  uint32_t mepc;
  asm volatile("csrr %0, mepc" : "=r"(mepc) :);
  return mepc;
}

static void set_mepc(uint32_t mepc) {
  asm volatile("csrw mepc, %0" : : "r"(mepc));
}

void handler_lsu_fault(void) {
  pmp_load_exception = true;

  uint32_t mepc = get_mepc();
  LOG_INFO("Load fault exception handler: mepc = 0x%x", mepc);

  // Check if the two least significant bits of the instruction are b11 (0x3),
  // which means that the trapped instruction is not compressed
  // (32bits = 4bytes), otherwise (16bits = 2bytes).
  //
  // NOTE:
  // with RISC-V "c" (compressed instructions extension), 32bit
  // instructions can start on 16bit boundary.
  //
  // Please see:
  // "“C” Standard Extension for Compressed Instructions, Version 2.0",
  // section 16.1.
  uint32_t fault_instruction = *((uint32_t *)mepc);
  bool not_compressed = (fault_instruction & 0x3) == 0x3;
  mepc = not_compressed ? (mepc + 4) : (mepc + 2);
  set_mepc(mepc);
}

static void pmp_configure_load_tor(void) {
  uintptr_t load_range_start =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];

  // Non-inclusive
  uintptr_t load_range_end =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_SIZE];

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsNone,
  };

  pmp_region_configure_result_t result = pmp_region_configure_tor(
      PMP_LOAD_REGION_ID, config, load_range_start, load_range_end);
  CHECK(result == kPmpRegionConfigureOk,
        "Load configuration failed, error code = %d", result);
}

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
};

bool test_main(void) {
  pmp_load_exception = false;
  char load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(!pmp_load_exception, "Load access violation before PMP configuration");

  pmp_configure_load_tor();

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the bottom of the range load");

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the top of the range load");

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET + 1];
  CHECK(!pmp_load_exception, "Load access violation on top of the range + 1");

  (void)load;

  return true;
}
