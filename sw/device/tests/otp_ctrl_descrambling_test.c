// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

typedef struct partition_data {
  dif_otp_ctrl_partition_t partition;
  size_t size;
} partition_data_t;

static const partition_data_t kPartitions[] = {
    {
        .partition = kDifOtpCtrlPartitionSecret0,
        .size =
            (OTP_CTRL_PARAM_SECRET0_SIZE - OTP_CTRL_PARAM_SECRET0_DIGEST_SIZE) /
            sizeof(uint64_t),
    },
    {
        .partition = kDifOtpCtrlPartitionSecret1,
        .size =
            (OTP_CTRL_PARAM_SECRET1_SIZE - OTP_CTRL_PARAM_SECRET1_DIGEST_SIZE) /
            sizeof(uint64_t),
    },
    {
        .partition = kDifOtpCtrlPartitionSecret2,
        .size =
            (OTP_CTRL_PARAM_SECRET2_SIZE - OTP_CTRL_PARAM_SECRET2_DIGEST_SIZE) /
            sizeof(uint64_t),
    },
};

static inline uint32_t lower(uint64_t dword) { return (uint32_t)dword; }

static inline uint32_t upper(uint64_t dword) { return (uint32_t)(dword >> 32); }

size_t compare_dword(const uint64_t *actual_arr, uint32_t part_idx,
                     uint32_t dword_idx, uint64_t expected) {
  const uint64_t actual = actual_arr[dword_idx];
  if (actual == expected) {
    return 0;
  } else {
    LOG_WARNING("SECRET%0d, dword %0d: 0x%08x%08x != 0x%08x%08x", part_idx,
                dword_idx, upper(actual), lower(actual), upper(expected),
                lower(expected));
    return 1;
  }
}

bool test_main(void) {
  dif_otp_ctrl_t otp_ctrl;

  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  // Number of 64-bit words that differ from the expected value; used to
  // determine overall test pass or failure.
  size_t dwords_diff = 0;

  // Iterate over the partitions that are scrambled and read them out via the
  // DAI.  This SW-based access is only possible because the partitions have not
  // been locked in/before this test.
  for (uint32_t i = 0; i < ARRAYSIZE(kPartitions); ++i) {
    const partition_data_t *partition = &kPartitions[i];
    uint64_t readout[partition->size];

    LOG_INFO("Checking partition SECRET%0d.", i);
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_read64_array(
        &otp_ctrl, partition->partition, 0, readout, ARRAYSIZE(readout)));

    // Compare values read from OTP to expected values stored in the OTP image.
    switch (i) {
      case 0:
        dwords_diff += compare_dword(readout, 0, 0, 0x749f1cb4a7daf4f5);
        dwords_diff += compare_dword(readout, 0, 1, 0x117dbd7aca3f7de6);
        dwords_diff += compare_dword(readout, 0, 2, 0xd6313735da1740e4);
        dwords_diff += compare_dword(readout, 0, 3, 0x1dc4b32c25ef2c31);
        CHECK(partition->size == 4, "Unexpected size of SECRET0 partition!");
        break;

      case 1:
        dwords_diff += compare_dword(readout, 1, 0, 0x8ed040844dde2dca);
        dwords_diff += compare_dword(readout, 1, 1, 0x8251c8921ed1a7fc);
        dwords_diff += compare_dword(readout, 1, 2, 0x038c1b4e7bd7394c);
        dwords_diff += compare_dword(readout, 1, 3, 0x434677540fdc9956);
        dwords_diff += compare_dword(readout, 1, 4, 0x5cc32c34646c9a9f);
        dwords_diff += compare_dword(readout, 1, 5, 0x871b3d2726a67336);
        dwords_diff += compare_dword(readout, 1, 6, 0xdcc70e44beeff5f4);
        dwords_diff += compare_dword(readout, 1, 7, 0x7cdb1a9d39c20016);
        dwords_diff += compare_dword(readout, 1, 8, 0x0e83fabc03c68203);
        dwords_diff += compare_dword(readout, 1, 9, 0x57f20b5b2e200c01);
        CHECK(partition->size == 10, "Unexpected size of SECRET1 partition!");
        break;

      case 2:
        dwords_diff += compare_dword(readout, 2, 0, 0xbed4fd235f6b24d4);
        dwords_diff += compare_dword(readout, 2, 1, 0x6ef5b95acb3ded39);
        dwords_diff += compare_dword(readout, 2, 2, 0xa9398fab0bba1e23);
        dwords_diff += compare_dword(readout, 2, 3, 0x196906bfe0051fa8);
        dwords_diff += compare_dword(readout, 2, 4, 0xea9f54f370a2fdf8);
        dwords_diff += compare_dword(readout, 2, 5, 0xf915734729d70391);
        dwords_diff += compare_dword(readout, 2, 6, 0xd3bd2ecfc0fc7581);
        dwords_diff += compare_dword(readout, 2, 7, 0xbaa7bc074a97c885);
        dwords_diff += compare_dword(readout, 2, 8, 0xdda3ceb51b6cbc3b);
        dwords_diff += compare_dword(readout, 2, 9, 0xe889c1ccf0f57d6d);
        CHECK(partition->size == 10, "Unexpected size of SECRET2 partition!");
        break;

      default:
        OT_UNREACHABLE();
        break;
    }
  }

  // Test succeeds if no value read from OTP differed from the expected value.
  return dwords_diff == 0;
}
