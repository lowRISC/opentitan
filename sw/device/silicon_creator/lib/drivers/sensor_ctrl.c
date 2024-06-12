// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/sensor_ctrl.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

enum {
  kBase = TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR,
  kSensorCtrlAlertConfig =
      OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_SENSOR_CTRL_ALERT_CFG_OFFSET,
  kSensorCtrlAlertSize = SENSOR_CTRL_ALERT_EN_MULTIREG_COUNT,
};

static_assert(kSensorCtrlAlertSize <=
                  OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_SENSOR_CTRL_ALERT_CFG_SIZE,
              "sensor_ctrl has more registers than OTP configuraiton bytes");

rom_error_t sensor_ctrl_configure(lifecycle_state_t lc_state) {
  switch (launder32(lc_state)) {
    case kLcStateProd:
    case kLcStateProdEnd:
    case kLcStateDev:
      // We don't need hardened checks for mission mode states because we intend
      // to program the sensor control block.
      //
      // We have hardened checks on the test and rma states because those states
      // skip programming.
      SEC_MMIO_WRITE_INCREMENT(kSensorCtrlSecMmioConfigure);
      break;
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return kErrorOk;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return kErrorOk;
    default:
      HARDENED_TRAP();
  }

  uint32_t val = 0;
  uint32_t fatal = 0;
  for (size_t i = 0; i < kSensorCtrlAlertSize; ++i) {
    // The OTP configuration words should be thought of as a single byte field
    // for each of the sensor_ctrl alert enables.  In each byte, the lower
    // nybble is a Mubi4 specifying whether to enable the alert and the upper
    // nybble is a Mubi4 specifying whether the alert is recoverable.
    val = otp_read32(kSensorCtrlAlertConfig + (i & ~3ul));
    uint32_t shift = 8 * (i % sizeof(uint32_t));
    sec_mmio_write32(
        kBase + SENSOR_CTRL_ALERT_EN_0_REG_OFFSET + i * sizeof(uint32_t),
        bitfield_field32_read(
            val, ((bitfield_field32_t){.mask = 0xF, .index = shift})));

    shift += 4;
    // The upper nybble will be Mubi4True (0x6) if the alert is recoverable and
    // Mubi4False (0x9) if fatal.  We XOR the lower three bits of the nybble
    // into the fatal-enable bit position for this alert.
    // When recoverable, the value will be zero (0 ^ 1 ^ 1).
    // When fatal, the value will be one: (1 ^ 0 ^ 0).
    fatal ^= (uint32_t)bitfield_bit32_read(val, shift++) << i;
    fatal ^= (uint32_t)bitfield_bit32_read(val, shift++) << i;
    fatal ^= (uint32_t)bitfield_bit32_read(val, shift++) << i;
  }
  sec_mmio_write32(kBase + SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, fatal);
  return kErrorOk;
}
