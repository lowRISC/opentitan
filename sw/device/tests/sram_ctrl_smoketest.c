// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// define a number of reads and writes to perform,
// for our purposes a small number will be sufficient.
#define SRAM_CTRL_TEST_DATA_SIZE_WORDS 16

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kStatusRegMask = kDifSramCtrlStatusBusIntegErr |
                                       kDifSramCtrlStatusInitErr |
                                       kDifSramCtrlStatusEscalated;

static const uint32_t kRandomData[SRAM_CTRL_TEST_DATA_SIZE_WORDS] = {
    0x6b4abfae, 0x63bdb6e7, 0x87f99b1a, 0xa214dffe, 0xb12291f9, 0xd0cd1abe,
    0x5c95e716, 0xe887aab1, 0x307f6ef9, 0x6f5c0464, 0x5882279d, 0x44c19574,
    0x1bd20079, 0xf8250ead, 0x4bf362a4, 0xad41437d};

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[SRAM_CTRL_TEST_DATA_SIZE_WORDS];

// Write / Read small chunks of data to SRAM to test
// basic functionality of sram_ctrl
static void write_read_check(mmio_region_t base_addr_region,
                             const char *sram_name) {
  uint32_t rw_data_32;
  for (int i = 0; i < SRAM_CTRL_TEST_DATA_SIZE_WORDS; ++i) {
    mmio_region_write32(base_addr_region, i * (ptrdiff_t)sizeof(uint32_t),
                        kRandomData[i]);
    rw_data_32 =
        mmio_region_read32(base_addr_region, i * (ptrdiff_t)sizeof(uint32_t));
    CHECK(rw_data_32 == kRandomData[i],
          "Memory Write/Read Mismatch for %s, index %d, data read = %08x "
          "data_expected = %08x.",
          sram_name, i, rw_data_32, kRandomData[i]);
  }
}

bool test_main(void) {
  // Initialize SRAM_CTRL hardware.
  dif_sram_ctrl_t sram_ctrl_main;
  dif_sram_ctrl_t sram_ctrl_ret;
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl_main));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl_ret));

  dif_sram_ctrl_status_bitfield_t status_main;
  dif_sram_ctrl_status_bitfield_t status_ret;

  // Check Status registers
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_ret, &status_ret));
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_main, &status_main));

  CHECK((status_main & kStatusRegMask) == 0x0,
        "SRAM main status error bits set, status = %08x.", status_main);
  CHECK((status_ret & kStatusRegMask) == 0x0,
        "SRAM ret status error bits set, status = %08x.", status_ret);

  // Read and Write to/from SRAMs. Main SRAM will use the address of the
  // buffer that has been allocated. Ret SRAM can start at the base address.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;

  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);
  mmio_region_t sram_region_ret_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR);

  // write / read checks
  write_read_check(sram_region_ret_base_addr, "SRAM_RET");
  write_read_check(sram_region_main_addr, "SRAM_MAIN");

  return true;
}
