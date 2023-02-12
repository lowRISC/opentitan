// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "otp_ctrl_regs.h"                            // Generated

OTTF_DEFINE_TEST_CONFIG();

/**
 * OTP HW partition relative IFETCH offset in bytes.
 *
 * x = OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET (1728)
 * y = OTP_CTRL_PARAM_HW_CFG_OFFSET (1664)
 * IFETCH_OFFSET = (x - y) = 64
 */
static const uint32_t kOtpIfetchHwRelativeOffset =
    OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET;

static const uint32_t kOtpEntropySrcFwReadOffset =
    (OTP_CTRL_PARAM_EN_ENTROPY_SRC_FW_READ_OFFSET -
     OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET) *
    8;

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 12,
};

/**
 * Configures the entropy source module in firmware override mode.
 *
 * Output is routed to firmware, and the fw_override mode is enabled to get data
 * post-health tests and before the pre conditioner block.
 *
 * @param entropy An entropy source instance.
 */
static void entropy_with_fw_override_enable(dif_entropy_src_t *entropy_src) {
  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = kEntropyFifoBufferSize,
  };
  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      entropy_src, fw_override_config, kDifToggleEnabled));

  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = true,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
  CHECK_DIF_OK(
      dif_entropy_src_configure(entropy_src, config, kDifToggleEnabled));
}

/**
 * Rounds known answer test for the entropy_src SHA-3 conditioner.
 *
 * This test uses the following SHA3 CAVP test vector:
 *
 * Msg=a90d2aa5b241e1ca9dab5b6dc05c3e2c93fc5a2210a6315d60f9b791b36b560d70e135ef8e7dba9441b74e53dab0606b
 * MD=4a16881ce156f45fdfdb45088e3f23be1b4c5a7a6a35315d36c51c75f275733319aca185d4ab33130ffe45f751f1bbc5
 *
 * See:
 * https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing
 */
static void test_fuse_init(dif_entropy_src_t *entropy) {
  CHECK_DIF_OK(dif_entropy_src_set_enabled(entropy, kDifToggleDisabled));
  entropy_with_fw_override_enable(entropy);
  CHECK_DIF_OK(dif_entropy_src_conditioner_start(entropy));

  const uint32_t kInputMsg[kEntropyFifoBufferSize] = {
      0xa52a0da9, 0xcae141b2, 0x6d5bab9d, 0x2c3e5cc0, 0x225afc93, 0x5d31a610,
      0x91b7f960, 0x0d566bb3, 0xef35e170, 0x94ba7d8e, 0x534eb741, 0x6b60b0da,
  };
  CHECK_DIF_OK(dif_entropy_src_observe_fifo_write(entropy, kInputMsg,
                                                  ARRAYSIZE(kInputMsg), NULL));

  CHECK_DIF_OK(dif_entropy_src_conditioner_stop(entropy));
}

void test_fuse_enable(dif_entropy_src_t *entropy) {
  test_fuse_init(entropy);

  uint32_t got[kEntropyFifoBufferSize];
  for (size_t i = 0; i < ARRAYSIZE(got); ++i) {
    CHECK_DIF_OK(dif_entropy_src_non_blocking_read(entropy, &got[i]));
  }

  const uint32_t kExpectedDigest[kEntropyFifoBufferSize] = {
      0x1c88164a, 0x5ff456e1, 0x0845dbdf, 0xbe233f8e, 0x7a5a4c1b, 0x5d31356a,
      0x751cc536, 0x337375f2, 0x85a1ac19, 0x1333abd4, 0xf745fe0f, 0xc5bbf151,
  };
  CHECK_ARRAYS_EQ(got, kExpectedDigest, kEntropyFifoBufferSize,
                  "Unexpected digest value.");
}

static void test_fuse_disable(dif_entropy_src_t *entropy) {
  enum {
    kAttemptsAmount = 4,
    kAttemptIntervalMicros = 500,
  };

  uint32_t got;
  test_fuse_init(entropy);
  for (uint32_t tries = 0; tries < kAttemptsAmount; --tries) {
    CHECK(dif_entropy_src_non_blocking_read(entropy, &got) == kDifUnavailable);
    busy_spin_micros(kAttemptIntervalMicros);
  }
}

/**
 * Read the otp at `HW_CFG.EN_ENTROPY_SRC_FW_READ` address and check whether is
 * configured by the `uvm_test_seq` as expected.
 *
 * @param expected Define the expected value for the
 * HW_CFG.EN_ENTROPY_SRC_FW_READ flag.
 */
static void check_entropy_src_fw_read_enable(bool expected) {
  dif_otp_ctrl_t otp;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
  otp_ctrl_testutils_wait_for_dai(&otp);

  uint32_t value;
  // Read the current value of the partition.
  CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(&otp, kDifOtpCtrlPartitionHwCfg,
                                           kOtpIfetchHwRelativeOffset));
  otp_ctrl_testutils_wait_for_dai(&otp);
  CHECK_DIF_OK(dif_otp_ctrl_dai_read32_end(&otp, &value));
  multi_bit_bool_t enable = bitfield_field32_read(
      value,
      (bitfield_field32_t){.mask = 0xff, .index = kOtpEntropySrcFwReadOffset});
  CHECK((enable == kMultiBitBool8True) == expected,
        "`fw_enable` not expected (%x)", enable);
}

/**
 * This test:
 *
 * - Initialize the OTP with the `HW_CFG.EN_ENTROPY_SRC_FW_READ` fuse bit set to
 * enabled in the `uvm_test_seq`.
 * - Read and verify the OTP `HW_CFG.EN_ENTROPY_SRC_FW_READ` against the
 * previous step expectation.
 * - Read the entropy_data_fifo via SW; verify that it reads valid values.
 * - Reset the chip, but this time, initialize the OTP with with the
 * `HW_CFG.EN_ENTROPY_SRC_FW_READ` fuse bit set to disable.
 * - Read and verify the OTP `HW_CFG.EN_ENTROPY_SRC_FW_READ` against the
 * previous step expectation.
 * - Read the internal state via SW; verify that the entropy valid bit is zero.
 */
bool test_main(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  info = rstmgr_testutils_reason_get();

  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time");
    check_entropy_src_fw_read_enable(true);
    test_fuse_enable(&entropy_src);
    // Reboot device.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // This log message is extremely important for the test, as the
    // `uvm_test_seq` uses it to change the otp values.
    LOG_INFO("Software resetting!");

    // Wait here until device reset.
    wait_for_interrupt();
  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Powered up for the second time");

    check_entropy_src_fw_read_enable(false);
    test_fuse_disable(&entropy_src);
    return true;
  }
  return false;
}
