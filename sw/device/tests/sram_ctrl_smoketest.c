// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_sram_ctrl.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

// Define a number of reads and writes to perform; for our purposes a small
// number will be sufficient.
#define SRAM_CTRL_TEST_DATA_SIZE_WORDS 16

static_assert(kDtSramCtrlCount >= 1,
              "This test requires at least one RAM Control instance");
static_assert(kDtSramCtrlCount < 100,
              "The reported SRAM_CTRL instance number may be incorrect");

#define SRAM_CTRL_NAME(x) #x

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kStatusRegMask = kDifSramCtrlStatusBusIntegErr |
                                       kDifSramCtrlStatusInitErr |
                                       kDifSramCtrlStatusEscalated;

static const uint32_t kRandomData[SRAM_CTRL_TEST_DATA_SIZE_WORDS] = {
    0x6b4abfae, 0x63bdb6e7, 0x87f99b1a, 0xa214dffe, 0xb12291f9, 0xd0cd1abe,
    0x5c95e716, 0xe887aab1, 0x307f6ef9, 0x6f5c0464, 0x5882279d, 0x44c19574,
    0x1bd20079, 0xf8250ead, 0x4bf362a4, 0xad41437d};

// Properties of each of the SRAM_CTRL blocks to be tested.
static struct {
  /**
   * Interface to SRAM_CTRL.
   */
  dif_sram_ctrl_t dif;
  /**
   * Base address of test buffer within SRAM_CTRL instance.
   */
  uintptr_t buf;
  /**
   * MMIO access to test buffer.
   */
  mmio_region_t region;
  /**
   * Name of SRAM_CTRL instance.
   */
  const char *name;
  /**
   * Name buffer, for those instances which are identified numerically.
   */
  char nameBuf[12];
} sram_ctrl[kDtSramCtrlCount];

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[SRAM_CTRL_TEST_DATA_SIZE_WORDS];

// Write and read small chunks of data to each SRAM_CTRL to test basic
// functionality; exercise all of the controllers in an interleaved fashion
// just to increase the chance of catching any crosstalk issues/interactions
// between the instances.
static void write_read_check(void) {
  for (int i = 0; i < SRAM_CTRL_TEST_DATA_SIZE_WORDS; ++i) {
    for (dt_sram_ctrl_t sc = (dt_sram_ctrl_t)0; sc < kDtSramCtrlCount; ++sc) {
      mmio_region_write32(sram_ctrl[sc].region, i * (ptrdiff_t)sizeof(uint32_t),
                          kRandomData[i]);
      uint32_t rw_data_32 = mmio_region_read32(sram_ctrl[sc].region,
                                               i * (ptrdiff_t)sizeof(uint32_t));
      CHECK(rw_data_32 == kRandomData[i],
            "Memory Write/Read Mismatch for %s, index %d, data read = %08x "
            "data_expected = %08x.",
            sram_ctrl[sc].name, i, rw_data_32, kRandomData[i]);
    }
  }
}

bool test_main(void) {
  // Initialize SRAM_CTRL blocks.
  for (dt_sram_ctrl_t sc = (dt_sram_ctrl_t)0; sc < kDtSramCtrlCount; ++sc) {
    CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(sc, &sram_ctrl[sc].dif));

    // Decide upon the buffer address to be used for this SRAM controller.
    switch (sc) {
      // Main SRAM will use the address of the buffer that has been allocated.
      case kDtSramCtrlMain:
        sram_ctrl[sc].buf = (uintptr_t)sram_main_buffer;
        sram_ctrl[sc].name = SRAM_CTRL_NAME(kDtSramCtrlMain);
        break;

      default:
        // Ret SRAM can start at the beginning of the owner section.
        sram_ctrl[sc].buf =
            (uintptr_t)dt_sram_ctrl_reg_block(sc, kDtSramCtrlRegBlockRam);
        // Assume that no target device has more than 100 SRAM_CTRL instances.
        unsigned dig = (unsigned)sc / 10;
        sram_ctrl[sc].nameBuf[0] = (char)('0' + dig);
        sram_ctrl[sc].nameBuf[1] = (char)('0' + ((unsigned)sc - dig * 10));
        sram_ctrl[sc].name = sram_ctrl[sc].nameBuf;
        break;
    }
    // Obtain access to the buffer.
    sram_ctrl[sc].region = mmio_region_from_addr(sram_ctrl[sc].buf);
  }

  // Check Status registers
  for (dt_sram_ctrl_t sc = (dt_sram_ctrl_t)0; sc < kDtSramCtrlCount; ++sc) {
    dif_sram_ctrl_status_bitfield_t status;
    CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl[sc].dif, &status));
    CHECK((status & kStatusRegMask) == 0x0,
          "SRAM %s status error bits set, status = %08x.", sram_ctrl[sc].name,
          status);
  }

  // Write/read to/from SRAMs.
  write_read_check();

  return true;
}
