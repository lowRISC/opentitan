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
  kDfuStateAppDetach,
  kDfuStateIdle,
  kDfuStateDnLoadSync,
  kDfuStateDnLoadBusy,
  kDfuStateDnLoadIdle,
  kDfuStateManifestSync,
  kDfuStateManifest,
  kDfuStateManifestWaitReset,
  kDfuStateUpLoadIdle,
  kDfuStateError,
  kDfuStateTotalLength,
} dfu_state_t;

/**
 * DFU error codes.
 */
typedef enum dfu_err {
  kDfuErrOk = 0,
  kDfuErrTarget,
  kDfuErrFile,
  kDfuErrWrite,
  kDfuErrErase,
  kDfuErrCheckErased,
  kDfuErrProg,
  kDfuErrVerify,
  kDfuErrAddress,
  kDfuErrNotDone,
  kDfuErrFirmware,
  kDfuErrVendor,
  kDfuErrUsbReset,
  kDfuErrPowerOnReset,
  kDfuErrUnknown,
  kDfuErrStalledPkt,
} dfu_err_t;

/**
 * DFU requests (e.g SETUPDATA `bRequest`).
 */
typedef enum dfu_req {
  kDfuReqDetach = 0,
  kDfuReqDnLoad,
  kDfuReqUpLoad,
  kDfuReqGetStatus,
  kDfuReqClrStatus,
  kDfuReqGetState,
  kDfuReqAbort,
  kDfuReqBusReset,
  kDfuReqTotalLength,
} dfu_req_t;

/**
 * DFU actions to take during a state transition.
 */
typedef enum dfu_action_t {
  kDfuActionNone = 0,
  kDfuActionStall,
  kDfuActionCheckLen,
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
  uint8_t action;
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
 * The DFU rescue context.
 */
typedef struct dfu_ctx {
  /** USB context for managing endpoint zero. */
  usb_control_ctx_t ep0;
  /** Rescue state. */
  rescue_state_t state;
  /** Pointer to bootdata. */
  boot_data_t *bootdata;
  /** Status buffer (used to respond to DfuReqGetStatus). */
  uint8_t status[6];
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
 * @param ep The endpoint number.
 * @param data The buffer to send or receive into.
 * @param len The length of the buffer.
 * @param flags The direction or other attributes assocated with the transfer.
 */
void dfu_transport_data(size_t ep, void *data, size_t len,
                        usb_transfer_flags_t flags);

/**
 * Handle the transport's standard setupdata requests
 *
 * This is a simple wrapper around `usb_control_setupdata` that can be replaced
 * at link-time with alternative transports (such as SPI).
 *
 * @param ctx A pointer to the transport's control context structure.
 * @param setup A pointer to the setupdata.
 * @return Result of handling the setupdata.
 */
rom_error_t dfu_transport_setupdata(usb_control_ctx_t *ctx,
                                    usb_setup_data_t *setup);

/**
 * Report a result or error on the transport.
 *
 * On USB, if there is an error, this should stall the control endpoint.
 *
 * @param result The Ok or Error result to signal on the transport.
 */
void dfu_transport_result(rom_error_t result);

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
void dfu_protocol_handler(void *ctx, size_t ep, usb_transfer_flags_t flags,
                          void *data);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_DFU_H_
