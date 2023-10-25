// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This test writes some data to SRAM, sets the `INIT` bit in the `ctrl` CSR,
//! then tries to read back that written data to ensure the SRAM was scrambled.
//!
//! The test currently only checks the retention SRAM so that it can be run out
//! of executable main SRAM on silicon.

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

// Define some amount of data we should leave in SRAM to check it gets wiped.
enum {
  kSramCtrlTestDataSizeWords = 16,
};

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kStatusRegMask = kDifSramCtrlStatusBusIntegErr |
                                       kDifSramCtrlStatusInitErr |
                                       kDifSramCtrlStatusEscalated;

static const uint32_t kRandomData[kSramCtrlTestDataSizeWords] = {
    0x6b4abfae, 0x63bdb6e7, 0x87f99b1a, 0xa214dffe, 0xb12291f9, 0xd0cd1abe,
    0x5c95e716, 0xe887aab1, 0x307f6ef9, 0x6f5c0464, 0x5882279d, 0x44c19574,
    0x1bd20079, 0xf8250ead, 0x4bf362a4, 0xad41437d};

/// Write `kRandomData` to an SRAM region.
static void write_data(mmio_region_t sram_region) {
  for (int i = 0; i < kSramCtrlTestDataSizeWords; ++i) {
    mmio_region_write32(sram_region, i * (ptrdiff_t)sizeof(uint32_t),
                        kRandomData[i]);
  }
}

/// Check that the contents of an SRAM region match `kRandomData`.
///
/// The `matches` arg is used to specify whether you expect the SRAM region to
/// match `kRandomData`, or whether it should have been re-scrambled and no
/// longer match.
static void check_data_matches(mmio_region_t sram_region, bool matches) {
  for (int i = 0; i < kSramCtrlTestDataSizeWords; ++i) {
    uint32_t word =
        mmio_region_read32(sram_region, i * (ptrdiff_t)sizeof(uint32_t));

    if (matches) {
      CHECK(word == kRandomData[i],
            "Data at index %u mismached, expected: %04x, got: %04x", i,
            kRandomData[i], word);
    } else if (word != kRandomData[i]) {
      return;
    }
  }

  // If we got to this point and expected _not_ to match, fail.
  CHECK(matches, "Data in SRAM was not rescrambled correctly");
}

/// (Re-)initialize an SRAM region with pseudorandom data.
static void init_sram(dif_sram_ctrl_t sram_ctrl) {
  uint32_t init = bitfield_bit32_write(0, SRAM_CTRL_CTRL_INIT_BIT, true);
  mmio_region_write32(sram_ctrl.base_addr, SRAM_CTRL_CTRL_REG_OFFSET, init);

  // Spin until SRAM_CTRL is ready.
  dif_sram_ctrl_status_bitfield_t status;
  do {
    CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl, &status));
  } while ((status & kDifSramCtrlStatusInitDone) == 0x0);

  CHECK((status & kStatusRegMask) == 0x0,
        "SRAM ret status error bits set, status = %08x.", status);
}

bool test_main(void) {
  // Initialize SRAM_CTRL hardware.
  dif_sram_ctrl_t sram_ctrl_ret;
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl_ret));

  init_sram(sram_ctrl_ret);

  uintptr_t sram_ret_buffer_addr =
      TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
      offsetof(retention_sram_t, owner);

  mmio_region_t sram_region_ret_addr =
      mmio_region_from_addr(sram_ret_buffer_addr);

  // Write some data to retention SRAM and read it back to validate.
  write_data(sram_region_ret_addr);
  // Read back the data to validate it was written.
  check_data_matches(sram_region_ret_addr, true);

  // Run initialization on the retention SRAM and check that the data is gone.
  init_sram(sram_ctrl_ret);
  check_data_matches(sram_region_ret_addr, false);

  return true;
}
