// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Device ID OTP offset and sizes.
   */
  kDeviceIdOffset =
      OTP_CTRL_PARAM_DEVICE_ID_OFFSET - OTP_CTRL_PARAM_HW_CFG0_OFFSET,
  kDeviceIdSizeInBytes = OTP_CTRL_PARAM_DEVICE_ID_SIZE,
  kDeviceIdSizeIn32BitWords = kDeviceIdSizeInBytes / sizeof(uint32_t),
};

static dif_pinmux_t pinmux;
static dif_otp_ctrl_t otp;

static const uint32_t kTestDeviceId[kDeviceIdSizeIn32BitWords] = {
    0xdeadbeef, 0x12345678, 0xabcdef12, 0xcafebeef,
    0x87654321, 0x21fedcba, 0xa1b2c3d4, 0xacdc4321,
};

/**
 * Initialize all DIF handles used in this program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  return OK_STATUS();
}

static status_t otp_ctrl_read_hw_cfg0_device_id(uint32_t *device_id) {
  for (size_t i = kDeviceIdOffset; i < kDeviceIdSizeIn32BitWords; ++i) {
    TRY(otp_ctrl_testutils_dai_read32(&otp, kDifOtpCtrlPartitionHwCfg0,
                                      kDeviceIdOffset + (i * 4),
                                      &device_id[i]));
    LOG_INFO("Device ID (%d) = %08x", i, device_id[i]);
  }
  return OK_STATUS();
}

/**
 * Check the Device ID has not yet been provisioned in OTP.
 *
 * The HW_CFG0 partition should be unlocked and the device ID should be all
 * zero.
 */
static status_t check_device_id_is_unprovisioned(void) {
  // Check HW_CFG0 is unlocked.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(&otp, kDifOtpCtrlPartitionHwCfg0,
                                      &is_locked));
  CHECK(!is_locked);

  // Check Device ID is all zeros.
  uint32_t expected_device_id[kDeviceIdSizeIn32BitWords] = {0};
  uint32_t actual_device_id[kDeviceIdSizeIn32BitWords] = {0};
  TRY(otp_ctrl_read_hw_cfg0_device_id(actual_device_id));
  CHECK_ARRAYS_EQ(actual_device_id, expected_device_id,
                  kDeviceIdSizeIn32BitWords);
  return OK_STATUS();
}

/**
 * Check the Device ID has been provisioned in OTP, but not locked.
 */
static status_t check_device_id_is_provisioned(void) {
  // Check HW_CFG0 is still unlocked.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(&otp, kDifOtpCtrlPartitionHwCfg0,
                                      &is_locked));
  CHECK(!is_locked);

  // Check Device ID matches what is expected.
  uint32_t actual_device_id[kDeviceIdSizeIn32BitWords] = {0};
  TRY(otp_ctrl_read_hw_cfg0_device_id(actual_device_id));
  CHECK_ARRAYS_EQ(actual_device_id, kTestDeviceId, kDeviceIdSizeIn32BitWords);
  return OK_STATUS();
}

/**
 * Provisions a Device ID into the HW_CFG0 OTP partition.
 */
static status_t provisioning_device_id_start(void) {
  LOG_INFO("Provisioning Device ID in OTP.");
  check_device_id_is_unprovisioned();
  TRY(otp_ctrl_testutils_dai_write32(&otp, kDifOtpCtrlPartitionHwCfg0,
                                     kDeviceIdOffset, kTestDeviceId,
                                     kDeviceIdSizeIn32BitWords));
  return OK_STATUS();
}

/**
 * Provisions a Device ID into the HW_CFG0 OTP partition.
 */
static status_t provisioning_device_id_end(void) {
  LOG_INFO("Provisioning complete.");
  check_device_id_is_provisioned();
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();

  CHECK_STATUS_OK(provisioning_device_id_start());
  CHECK_STATUS_OK(provisioning_device_id_end());

  test_status_set(kTestStatusPassed);
  return true;
}
