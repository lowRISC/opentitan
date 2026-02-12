// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_RESCUE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_RESCUE_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
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
  /** `KLBR` */
  kRescueModeKlobber = 0x4b4c4252,
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
  /** `NOOP` */
  kRescueModeNoOp = 0x4e4f4f50,
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
  // Current rescue mode.
  rescue_mode_t mode;
  // Default rescue mode.
  rescue_mode_t default_mode;
  // Inactivity deadline.
  uint64_t inactivity_deadline;
  // Current xmodem frame.
  uint32_t frame;
  // Current data offset.
  uint32_t offset;
  // Amount of data staged in the `data` buffer (for data to send to the host).
  uint16_t staged_len;
  // Current flash write offset.
  uint32_t flash_offset;
  // Current flash beginning offset.  This is the partition-relative offset
  // where we're allowed to start writing to flash.  Normally, this will be
  // the same as `flash_start`, but if we're allowed to write the ROM_EXT
  // and we've detected a ROM_EXT, this may be adjusted to zero.
  uint32_t flash_begin;
  // Range to erase and write for firmware rescue (inclusive).
  uint32_t flash_start;
  uint32_t flash_limit;
  // Pointer to the current bootdata record.
  boot_data_t *bootdata;
  // Pointer to the boot log.
  boot_log_t *boot_log;
  // Rescue configuration.
  const owner_rescue_config_t *config;
  // Data buffer to hold xmodem upload data.
  uint8_t data[2048];
} rescue_state_t;

extern const uint32_t rescue_type;

/**
 * Handle rescue modes that involve sending data to the host.
 *
 * @param state Rescue state
 * @return kErrorOk if nothing to do, kErrorRescueSendStart if the state->data
 *         buffer is ready to send, or an error.
 */
rom_error_t rescue_send_handler(rescue_state_t *state);

/**
 * Handle rescue movdes that involve receiving data into the device.
 *
 * @param state Rescue state
 * @return kErrorOk if no error or an error code indicating a problem with
 *         the received data.
 */
rom_error_t rescue_recv_handler(rescue_state_t *state);

/**
 * Validate a new rescue mode.
 *
 * @param mode The new mode.
 * @param state Rescue state
 * @return kErrorOk if the new mode was accepted, kErrorBadMode otherwise.
 *
 * The rescue state is updated: mode, offset and flash_offset.
 */
rom_error_t rescue_validate_mode(uint32_t mode, rescue_state_t *state);

/**
 * Initialize the rescue state.
 *
 * @param state Rescue state
 * @param bootdata Boot data
 * @param boot_log The boot_log
 * @param config The ownership rescue config (if any).
 */
void rescue_state_init(rescue_state_t *state, boot_data_t *bootdata,
                       boot_log_t *boot_log,
                       const owner_rescue_config_t *config);

/**
 * Handle the boot services RescueEnter request.
 *
 * @param msg The boot services message.
 * @return kErrorOk if the command was processed correctly.
 */
rom_error_t rescue_enter_handler(boot_svc_msg_t *msg);

/**
 * Return an error if the inactivity deadline has passed.
 *
 * @param state Rescue state
 * @return kErrorOk if the deadline has not passed,
 *         kErrorRescueInactivity if it has.
 */
rom_error_t rescue_inactivity(rescue_state_t *state);

/**
 * Perform the rescue protocol.
 *
 * @param bootdata Boot data
 * @param boot_log The boot_log
 * @param config The ownership rescue config (if any).
 * @return Any error in processing the rescue protocol.
 */
rom_error_t rescue_protocol(boot_data_t *bootdata, boot_log_t *boot_log,
                            const owner_rescue_config_t *config);

/**
 * Enter rescue mode on boot failure.
 * @param config The ownership rescue config (if any).
 * @return whether to enter rescue mode.
 */
hardened_bool_t rescue_enter_on_fail(const owner_rescue_config_t *config);

/**
 * Send ourself a message to skip rescue entry on the next boot.
 */
void rescue_skip_next_boot(void);

/**
 * Detect rescue entry.
 *
 * @param config The ownership rescue config (if any).
 * @return kHardenedBoolTrue if we should enter rescue mode.
 */
hardened_bool_t rescue_detect_entry(const owner_rescue_config_t *config);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_RESCUE_H_
