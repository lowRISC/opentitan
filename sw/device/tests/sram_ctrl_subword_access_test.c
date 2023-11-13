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
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kSramCtrlTestDataSizeWords = 3,
  kSramCtrlTestDataSizeBytes = kSramCtrlTestDataSizeWords * 4,
};

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kStatusRegMask = kDifSramCtrlStatusBusIntegErr |
                                       kDifSramCtrlStatusInitErr |
                                       kDifSramCtrlStatusEscalated;

static const uint32_t kRandomData[kSramCtrlTestDataSizeWords] = {
    0x6b4abfae, 0x63bdb6e7, 0x87f99b1a};

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[kSramCtrlTestDataSizeWords];

/// Write `kRandomData` to SRAM, then read back a u8, u16, u32, and u64 from
/// each possible byte offset.
static void read_subwords_check(mmio_region_t region) {
  mmio_region_memcpy_to_mmio32(region, 0, kRandomData,
                               kSramCtrlTestDataSizeBytes);

  // Check byte reads.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes; ++i) {
    uint8_t expected = ((volatile uint8_t *)kRandomData)[i];
    uint8_t got = ((volatile uint8_t *)region.base)[i];
    CHECK(expected == got,
          "byte %d read back incorrectly: expected %02x, got %02x", i, expected,
          got);
  }

  // Check uint16_t reads.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes - 1; ++i) {
    uint16_t expected = *(volatile uint16_t *)((uint8_t *)kRandomData + i);
    uint16_t got = *(volatile uint16_t *)((uint8_t *)region.base + i);
    CHECK(expected == got,
          "uint16_t %d read back incorrectly: expected %04x, got %04x", i,
          expected, got);
  }

  // Check uint32_t reads.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes - 3; ++i) {
    uint32_t expected = *(volatile uint32_t *)((uint8_t *)kRandomData + i);
    uint32_t got = *(volatile uint32_t *)((uint8_t *)region.base + i);
    CHECK(expected == got,
          "uint32_t %d read back incorrectly: expected %08x, got %08x", i,
          expected, got);
  }

  // Check uint64_t reads.
  for (uint64_t i = 0; i < kSramCtrlTestDataSizeBytes - 7; ++i) {
    uint64_t expected = *(volatile uint64_t *)((uint8_t *)kRandomData + i);
    uint64_t got = *(volatile uint64_t *)((uint8_t *)region.base + i);
    CHECK(expected == got,
          "uint64_t %d read back incorrectly: expected %08x%08x, got %08x%08x",
          i, (uint32_t)(expected >> 32), (uint32_t)expected,
          (uint32_t)(got >> 32), (uint32_t)got);
  }
}

/// Clear a whole SRAM region.
static void clear_sram_region(mmio_region_t region) {
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeWords; ++i) {
    mmio_region_write32(region, (ptrdiff_t)i, 0);
  }
}

/// Check that the contents of an SRAM region match the bytes of `kRandomData`
/// at a given byte offset and byte length.
static void check_sram_contents(mmio_region_t region, uint32_t offset,
                                uint32_t len) {
  for (uint32_t i = 0; i < len; ++i) {
    uint8_t expected = ((uint8_t *)kRandomData)[offset + i];
    uint8_t got = mmio_region_read8(region, (ptrdiff_t)(offset + i));
    CHECK(expected == got, "byte %d did not match: expected %02x, got %02x",
          offset + i, expected, got);
  }
}

/// Write each of a u8, u16, u32, and u64 from to every possible byte offset in
/// SRAM, reading them back to check the writes.
static void write_subwords_check(mmio_region_t region) {
  // Check byte writes.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes; ++i) {
    clear_sram_region(region);
    ((volatile uint8_t *)region.base)[i] = ((uint8_t *)kRandomData)[i];
    check_sram_contents(region, i, 1);
  }

  // Check uint16_t writes.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes - 1; ++i) {
    clear_sram_region(region);
    *(volatile uint16_t *)((uint8_t *)region.base + i) =
        *(uint16_t *)((uint8_t *)kRandomData + i);
    check_sram_contents(region, i, 2);
  }

  // Check uint32_t writes.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes - 3; ++i) {
    clear_sram_region(region);
    *(volatile uint32_t *)((uint8_t *)region.base + i) =
        *(uint32_t *)((uint8_t *)kRandomData + i);
    check_sram_contents(region, i, 4);
  }

  // Check uint64_t writes.
  for (uint32_t i = 0; i < kSramCtrlTestDataSizeBytes - 7; ++i) {
    clear_sram_region(region);
    *(volatile uint64_t *)((uint8_t *)region.base + i) =
        *(uint64_t *)((uint8_t *)kRandomData + i);
    check_sram_contents(region, i, 8);
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

  // Check Status registers.
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_ret, &status_ret));
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_main, &status_main));

  CHECK((status_main & kStatusRegMask) == 0x0,
        "SRAM main status error bits set, status = %08x.", status_main);
  CHECK((status_ret & kStatusRegMask) == 0x0,
        "SRAM ret status error bits set, status = %08x.", status_ret);

  // Read and Write to/from SRAMs. Main SRAM will use the address of the
  // buffer that has been allocated.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  // Ret SRAM will start at the beginning of the owner section, allowing this
  // test to run on silicon where creator SRAM is in use.
  uintptr_t sram_ret_buffer_addr =
      TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
      offsetof(retention_sram_t, owner);

  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);
  mmio_region_t sram_region_ret_base_addr =
      mmio_region_from_addr(sram_ret_buffer_addr);

  // Subword read checks.
  LOG_INFO("Checking subword reads on SRAM_RET");
  read_subwords_check(sram_region_ret_base_addr);
  LOG_INFO("Checking subword reads on SRAM_MAIN");
  read_subwords_check(sram_region_main_addr);

  // Subword write checks.
  LOG_INFO("Checking subword writes on SRAM_RET");
  write_subwords_check(sram_region_ret_base_addr);
  LOG_INFO("Checking subword writes on SRAM_MAIN");
  write_subwords_check(sram_region_main_addr);

  return true;
}
