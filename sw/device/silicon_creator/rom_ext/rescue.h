// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

enum {
  // Rescue is signalled by asserting serial break to the UART for at least
  // 4 byte periods.  At 115200 bps, one byte period is about 87us; four is
  // about 348us.  We'll wait for 350.
  kRescueDetectTime = 350,
};

typedef enum {
  /** `BLOG` */
  kRescueModeBootLog = 0x424c4f47,
  /** `BRSP` */
  kRescueModeBootSvcRsp = 0x42525350,
  /** `BREQ` */
  kRescueModeBootSvcReq = 0x42524551,
  /** `OWNR` */
  kRescueModeOwnerBlock = 0x4f574e52,
  /** `RESQ` */
  kRescueModeFirmware = 0x52455351,
  /** `REBO` */
  kRescueModeReboot = 0x5245424f,
  /** `DWIM` */
  kRescueModeDWIM = 0x4457494d,
} rescue_mode_t;

typedef struct RescueState {
  rescue_mode_t mode;
  uint32_t frame;
  uint32_t offset;
  uint32_t flash_offset;
  uint32_t flash_start;
  uint32_t flash_limit;
  uint8_t data[2048];
} rescue_state_t;

rom_error_t rescue_protocol(void);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_RESCUE_H_
