// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_DFU_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_DFU_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * DFU states.
 */
typedef enum dfu_state {
  kDfuStateAppIdle = 0,
  kDfuStateAppDetach = 1,
  kDfuStateIdle = 2,
  kDfuStateDnLoadSync = 3,
  kDfuStateDnLoadBusy = 4,
  kDfuStateDnLoadIdle = 5,
  kDfuStateManifestSync = 6,
  kDfuStateManifest = 7,
  kDfuStateManifestWaitReset = 8,
  kDfuStateUpLoadIdle = 9,
  kDfuStateError = 10,
  kDfuStateTotalLength = 11,
} dfu_state_t;

/**
 * DFU error codes.
 */
typedef enum dfu_err {
  kDfuErrOk = 0,
  kDfuErrTarget = 1,
  kDfuErrFile = 2,
  kDfuErrWrite = 3,
  kDfuErrErase = 4,
  kDfuErrCheckErased = 5,
  kDfuErrProg = 6,
  kDfuErrVerify = 7,
  kDfuErrAddress = 8,
  kDfuErrNotDone = 9,
  kDfuErrFirmware = 10,
  kDfuErrVendor = 11,
  kDfuErrUsbReset = 12,
  kDfuErrPowerOnReset = 13,
  kDfuErrUnknown = 14,
  kDfuErrStalledPkt = 15,
} dfu_err_t;

/**
 * DFU requests (e.g SETUPDATA `bRequest`).
 */
typedef enum dfu_req {
  kDfuReqDetach = 0,
  kDfuReqDnLoad = 1,
  kDfuReqUpLoad = 2,
  kDfuReqGetStatus = 3,
  kDfuReqClrStatus = 4,
  kDfuReqGetState = 5,
  kDfuReqAbort = 6,
  kDfuReqTotalLength = 7,
} dfu_req_t;

/**
 * DFU actions to take during a state transition.
 */
typedef enum dfu_action_t {
  kDfuActionNone = 0,
  kDfuActionStall,
  kDfuActionDataXfer,
  kDfuActionStatusResponse,
  kDfuActionStateResponse,
  kDfuActionClearError,
  kDfuActionReset,
} dfu_action_t;

/**
 * A DFU state transition.
 *
 * The action in taken and then a next state is chosen based on the action's
 * result.
 */
typedef struct dfu_state_transition {
  /**
   * Holds a `dfu_action_t` specifying which action to take for the state
   * transition.
   */
  uint8_t action;
  /**
   * Holds `dfu_state_t`.  Depending on the result of the `action`, the next
   * state will be either next[0] or next[1].
   */
  uint8_t next[2];
} dfu_state_transition_t;

/**
 * The DFU state table mapping actions and next states.
 *
 * We map determine the next state for each DFU request and initial state.
 */
extern dfu_state_transition_t dfu_state_table[kDfuReqTotalLength]
                                             [kDfuStateTotalLength];

/**
 * The response to a DFU_GETSTATUS request.
 */
typedef struct dfu_getstatus {
  /** The status of the most recent request. */
  uint8_t status;
  /** Minimum time (ms) that the host should wait before sending another
   * DFU_GETSTATUS request. */
  uint8_t poll_timeout[3];
  /** The next state of the device after this response. */
  uint8_t state;
  /** An index of the status description in the string table. */
  uint8_t string;
} dfu_getstatus_t;

/**
 * The DFU rescue context.
 */
typedef struct dfu_ctx {
  /** USB context for managing endpoint zero. */
  usb_control_ctx_t ep0;
  /** Rescue state. */
  rescue_state_t state;
  /** Pointer to bootdata. */
  boot_data_t *bootdata;
  /** Expected receive length (upload) */
  uint32_t expected_len;
  /** Status buffer (used to respond to DfuReqGetStatus). */
  dfu_getstatus_t status;
  /** DFU state. */
  uint8_t dfu_state;
  /** DFU error. */
  uint8_t dfu_error;
  /** Currenty selected usb interface setting. */
  uint8_t interface;
} dfu_ctx_t;

/**
 * Start a DFU transfer.
 *
 * This is a simple wrapper around `usb_ep_transfer` that can be replaced at
 * link-time with alternative transports (such as SPI).
 *
 * @param ctx The DFU context.
 * @param dir The direction of the transfer.
 * @param data The buffer to send or receive into.
 * @param len The length of the buffer.
 * @param flags The direction or other attributes assocated with the transfer.
 */
void dfu_transport_data(dfu_ctx_t *ctx, usb_dir_t dir, void *data, size_t len,
                        usb_transfer_flags_t flags);

/**
 * Handle the transport's standard setupdata requests
 *
 * This is a simple wrapper around `usb_control_setupdata` that can be replaced
 * at link-time with alternative transports (such as SPI).
 *
 * @param ctx The DFU context.
 * @param setup A pointer to the setupdata.
 * @return Result of handling the setupdata.
 */
rom_error_t dfu_transport_setupdata(dfu_ctx_t *ctx, usb_setup_data_t *setup);

/**
 * Report a result or error on the transport.
 *
 * On USB, if there is an error, this should stall the control endpoint.
 *
 * @param ctx The DFU context.
 * @param result The Ok or Error result to signal on the transport.
 */
void dfu_transport_result(dfu_ctx_t *ctx, rom_error_t result);

/**
 * Implements the DFU protocol.
 *
 * For USB, this is the endpoint callback function.
 *
 * @param ctx A pointer to a `dfu_ctx_t`.
 * @param ep The endpoint number for the callback.
 * @param flags The condition for the callback.
 * @param data Any extra data associated with the condition.
 */
void dfu_protocol_handler(void *ctx, uint8_t ep, usb_transfer_flags_t flags,
                          void *data);

/**
 * Implementation constant.
 */
enum {
  /**
   * Device Class, SubClass and Protocol for DFU.
   */
  kDfuDeviceClass = 0xFE,
  kDfuDeviceSubClass = 0x01,
  kDfuDeviceProtocol = 0x02,

  /**
   * Constants for the DFU functional descriptor.
   */
  kDfuFuncDescLen = 9,
  kDfuFuncDescType = 0x21,
  kDfuFuncAttrCanDnLoad = 1,
  kDfuFuncAttrCanUpLoad = 2,
  kDfuFuncAttrManifestTolerant = 4,
  kDfuFuncAttrWillDetach = 8,
  kDfuFuncDetachTimeout = 32768,

  /**
   * We support a DFU transfer size of 2048.
   * This needs to be the same size as the rescue_state_t::buffer.
   */
  kDfuTransferSize = 2048,

  /**
   * The DFU version is 1.1.
   */
  kDfuMajorVersion = 1,
  kDfuMinorVersion = 1,

  /**
   * Vendor and Product IDs for the ROM_EXT.
   * Since lowRISC does not yet have a USB vendor ID, Google has reserved
   * product ID 0x023A to represent the OpenTitan ROM_EXT when in DFU
   * rescue mode.
   */
  kUsbVendorGoogle = 0x18d1,
  kUsbProuctRomExt = 0x023a,

  /**
   * A proprietary vendor request to set the DFU mode using a FourCC code
   * instead of an AltSetting index. The FourCC code uses the SETUP_DATA 16-bit
   * value and index fields to represent the 32-bit code.
   */
  kDfuVendorSetMode = 0x0b,

};

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_DFU_H_
