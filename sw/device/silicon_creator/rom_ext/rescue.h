// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

enum {
  // Rescue is signalled by asserting serial break to the UART for at least
  // 4 byte periods.  At 115200 bps, one byte period is about 87us; four is
  // about 348us.  We'll wait for 350.
  kRescueDetectTime = 350,
};

typedef enum {
  /** `BAUD` */
  kRescueModeBaud = 0x42415544,
  /** `BLOG` */
  kRescueModeBootLog = 0x424c4f47,
  /** `BRSP` */
  kRescueModeBootSvcRsp = 0x42525350,
  /** `BREQ` */
  kRescueModeBootSvcReq = 0x42524551,
  /** `OWNR` */
  kRescueModeOwnerBlock = 0x4f574e52,
  /** `OPG0` */
  kRescueModeOwnerPage0 = 0x4f504730,
  /** `OPG1` */
  kRescueModeOwnerPage1 = 0x4f504731,
  /** `OTID` */
  kRescueModeOpenTitanID = 0x4f544944,
  /** `RESQ` */
  kRescueModeFirmware = 0x52455351,
  /** `RESB` */
  kRescueModeFirmwareSlotB = 0x52455342,
  /** `REBO` */
  kRescueModeReboot = 0x5245424f,
  /** `WAIT` */
  kRescueModeWait = 0x57414954,
} rescue_mode_t;

typedef enum {
  /** `115K` */
  kRescueBaud115K = 0x4b353131,
  /** `230K` */
  kRescueBaud230K = 0x4b303332,
  /** `460K` */
  kRescueBaud460K = 0x4b303634,
  /** `921K` */
  kRescueBaud921K = 0x4b313239,
  /** `1M33` */
  kRescueBaud1M33 = 0x33334d31,
  /** `1M50` */
  kRescueBaud1M50 = 0x30354d31,
} rescue_baud_t;

typedef struct RescueState {
  rescue_mode_t mode;
  // Whether to reboot automatically after an xmodem upload.
  bool reboot;
  // Current xmodem frame.
  uint32_t frame;
  // Current data offset.
  uint32_t offset;
  // Current flash write offset.
  uint32_t flash_offset;
  // Range to erase and write for firmware rescue (inclusive).
  uint32_t flash_start;
  uint32_t flash_limit;
  // Rescue configuration.
  const owner_rescue_config_t *config;
  // Data buffer to hold xmodem upload data.
  uint8_t data[2048];
} rescue_state_t;

rom_error_t rescue_protocol(boot_data_t *bootdata,
                            const owner_rescue_config_t *rescue);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_
