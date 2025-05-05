// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rescue/dfu.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

typedef struct rescue_mode_properties {
  uint32_t mode;
  bool dnload;
  bool upload;
} rescue_mode_properties_t;

static const rescue_mode_properties_t mode_by_altsetting[] = {
    {kRescueModeFirmware, true, false},
    {kRescueModeFirmwareSlotB, true, false},
    {kRescueModeOpenTitanID, false, true},
    {kRescueModeBootLog, false, true},
    {kRescueModeBootSvcRsp, true, true},
    {kRescueModeOwnerPage0, true, true},
    //{ kRescueModeOwnerPage1, false, true },
};

static rom_error_t validate_mode(uint32_t setting, rescue_state_t *state) {
  // Allow the `setting` to be either an index or a FourCC code.
  // The the integer value is less than the arraysize, then its clearly an
  // index.
  if (setting >= ARRAYSIZE(mode_by_altsetting)) {
    // All of the FourCC codes are going to be greater than any index.  Search
    // the array for a matching FourCC code and use the index as the setting.
    size_t i = 0;
    for (; i < ARRAYSIZE(mode_by_altsetting); ++i) {
      if (setting == mode_by_altsetting[i].mode) {
        setting = i;
        break;
      }
    }
  }
  if (setting >= ARRAYSIZE(mode_by_altsetting)) {
    // Setting not found; Bad mode.
    return kErrorRescueBadMode;
  }

  // The UART version of the protocol has to distinguish between send and recv
  // targets for the same service (e.g. boot service has a request and a
  // response mode).  Since DFU supports upload and download operations to the
  // same target, we handle the "send" services first to stage data into the
  // rescue buffer.
  const rescue_mode_properties_t *mode = &mode_by_altsetting[setting];
  rom_error_t error2 = kErrorOk;
  rom_error_t error = rescue_validate_mode(mode->mode, state);

  // If the service exclusively supports either upload or download operation,
  // report bad mode immediately if a prior error occurred.
  if (!(mode->upload && mode->dnload)) {
    if (error != kErrorOk) {
      return kErrorRescueBadMode;
    }
  }

  if (error == kErrorOk && mode->upload) {
    // DFU upload means send to the host.  We stage the data that would
    // be sent to the rescue buffer.
    rescue_send_handler(state);
  }
  // BootSvc and OwnerPage are also recv (from the host) services.  Make sure
  // we're set up to process a DFU download for those services.
  if (mode->mode == kRescueModeBootSvcRsp) {
    error2 = rescue_validate_mode(kRescueModeBootSvcReq, state);
  } else if (mode->mode == kRescueModeOwnerPage0) {
    error2 = rescue_validate_mode(kRescueModeOwnerBlock, state);
  }

  if (error == kErrorOk || error2 == kErrorOk) {
    // If either the send or recv mode is ok, then setting the mode is ok.
    // If only one is Ok, the send or recv handler will report the error when we
    // try an unauthorized operation.
    return kErrorOk;
  }
  // If neither is Ok, the report bad mode.
  return kErrorRescueBadMode;
}

static rom_error_t dfu_control(dfu_ctx_t *ctx, usb_setup_data_t *setup) {
  rom_error_t result = kErrorOk;
  if (setup->request > kDfuReqAbort) {
    ctx->dfu_state = kDfuStateError;
    ctx->dfu_error = kDfuErrUnknown;
    return kErrorUsbBadSetup;
  }

  // Cancel the inactivity deadline.
  ctx->state.inactivity_deadline = 0;
  dfu_state_transition_t *tr = &dfu_state_table[setup->request][ctx->dfu_state];

  // Carry out the action for this state transition.
  switch (tr->action) {
    case kDfuActionNone:
      // No action: move to the next state and ack the transaction.
      ctx->dfu_state = tr->next[0];
      dfu_transport_data(ctx, kUsbDirIn, NULL, 0, 0);
      break;
    case kDfuActionStall:
      // Stall: move to the next state and stall the transport.
      ctx->dfu_state = tr->next[0];
      ctx->dfu_error = kDfuErrStalledPkt;
      result = kErrorUsbBadSetup;
      break;
    case kDfuActionDataXfer:
      // Check the length and download/upload.
      // DFU-spec quirks:
      // - We require that DnLoad transfers are always 2K blocks.  The last
      //   block is allowed to be short.
      // - We limit UpLoad transfers to a maximum of 2K.  We currently have
      //   no ROM_EXT services that require more than a 2K UpLoad.
      ctx->dfu_state = tr->next[setup->length == 0 ? 0 : 1];
      // Length is good and the request is either upload/download.
      if (setup->length <= sizeof(ctx->state.data) &&
          (setup->request == kDfuReqDnLoad ||
           setup->request == kDfuReqUpLoad)) {
        if (setup->request == kDfuReqDnLoad) {
          if (setup->length == 0 ||
              ctx->state.offset < ctx->state.flash_limit) {
            // If its a download (transfer to opentitan), perform the transfer
            // into the rescue state buffer. For a zero-length request, simply
            // ACK with a zero-length packet.
            dfu_transport_data(ctx, setup->length == 0 ? kUsbDirIn : kUsbDirOut,
                               ctx->state.data, setup->length, 0);
          } else {
            ctx->dfu_state = kDfuStateError;
            ctx->dfu_error = kDfuErrAddress;
            result = kErrorUsbBadSetup;
          }
        } else {
          // If its an upload (transfer to the host), perform the transfer
          // from the rescue state buffer. A prior `SetInterface` command will
          // have staged the requested content into the buffer.
          size_t length = (size_t)MIN(ctx->state.staged_len, setup->length);
          usb_transfer_flags_t flags =
              length < setup->length && length % 64 == 0
                  ? kUsbTransferFlagsShortIn
                  : 0;
          dfu_transport_data(ctx, kUsbDirIn, ctx->state.data, length, flags);
        }
      } else {
        ctx->dfu_state = kDfuStateError;
        ctx->dfu_error = kDfuErrUnknown;
        result = kErrorUsbBadSetup;
      }
      break;
    case kDfuActionStatusResponse:
      // Send a status response to the host.
      ctx->dfu_state = tr->next[0];
      ctx->status.status = (uint8_t)ctx->dfu_error;
      ctx->status.poll_timeout[0] = 100;  // poll us every 100 milliseconds.
      ctx->status.poll_timeout[1] = 0;
      ctx->status.poll_timeout[2] = 0;
      ctx->status.state = (uint8_t)ctx->dfu_state;
      ctx->status.string = 0;
      dfu_transport_data(ctx, kUsbDirIn, &ctx->status, sizeof(ctx->status), 0);
      break;
    case kDfuActionStateResponse:
      // Send our current DFU state to the host.
      ctx->dfu_state = tr->next[0];
      dfu_transport_data(ctx, kUsbDirIn, &ctx->dfu_state, 1, 0);
      break;
    case kDfuActionClearError:
      // Clear the current error.
      ctx->dfu_state = tr->next[0];
      ctx->dfu_error = kDfuErrOk;
      dfu_transport_data(ctx, kUsbDirIn, NULL, 0, 0);
      break;
  }

  return result;
}

static rom_error_t vendor_request(dfu_ctx_t *ctx, usb_setup_data_t *setup) {
  // Cancel the inactivity deadline.
  ctx->state.inactivity_deadline = 0;

  switch (setup->request) {
    // Proprietary vendor version of SetInterface that constructs the
    // FourCC from the value and index fields.
    case kDfuVendorSetMode: {
      uint32_t mode = ((uint32_t)setup->value << 16) | setup->index;
      if (validate_mode(mode, &ctx->state) == kErrorOk) {
        dfu_transport_data(ctx, kUsbDirIn, NULL, 0, 0);
      } else {
        return kErrorUsbBadSetup;
      }
    } break;
    default:
      return kErrorUsbBadSetup;
  }
  return kErrorOk;
}

static rom_error_t interface_request(dfu_ctx_t *ctx, usb_setup_data_t *setup) {
  switch (setup->request) {
    case kUsbSetupReqSetInterface:
      if (validate_mode(setup->value, &ctx->state) == kErrorOk) {
        // A typical OS USB stack will issue SET_INTERFACE to activate
        // AltSetting 0.  Since this probably is not real user activity,
        // we won't cancel the inactivity deadline for this action when it
        // doesn't actually change the interface.  For all other SET_INTERFACE,
        // we will cancel the inactivity deadline.
        if (!(ctx->interface == 0 && setup->value == 0)) {
          ctx->state.inactivity_deadline = 0;
        }
        ctx->interface = (uint8_t)setup->value;
        dfu_transport_data(ctx, kUsbDirIn, NULL, 0, 0);
      } else {
        return kErrorUsbBadSetup;
      }
      break;
    case kUsbSetupReqGetInterface:
      dfu_transport_data(ctx, kUsbDirIn, &ctx->interface,
                         sizeof(ctx->interface), 0);
      break;
    default:
      return kErrorUsbBadSetup;
  }
  return kErrorOk;
}

static rom_error_t set_configuration(dfu_ctx_t *ctx) {
  ctx->dfu_error = kDfuErrOk;
  ctx->dfu_state = kDfuStateIdle;
  ctx->interface = 0;
  validate_mode(ctx->interface, &ctx->state);
  ctx->ep0.configuration = ctx->ep0.next.configuration;
  return kErrorOk;
}

void dfu_protocol_handler(void *_ctx, uint8_t ep, usb_transfer_flags_t flags,
                          void *data) {
  dfu_ctx_t *ctx = (dfu_ctx_t *)_ctx;
  OT_DISCARD(ep);

  // Handle event callbacks from the underlying transport (e.g. USB).

  // If its SETUPDATA, its a USB or DFU request.
  if (flags & kUsbTransferFlagsSetupData) {
    usb_setup_data_t *setup = (usb_setup_data_t *)data;

    // If we receive any Class, Interface or Vendor specific request,
    // we cancel the inactivity deadline.
    rom_error_t error = kErrorOk;
    if ((setup->request_type & kUsbReqTypeTypeMask) == kUsbReqTypeClass) {
      // If its a class-level request, call the DFU control function.
      error = dfu_control(ctx, setup);
    } else if ((setup->request_type & kUsbReqTypeTypeMask) ==
               kUsbReqTypeVendor) {
      // If its a proprietary vendor request, we handle it here.
      error = vendor_request(ctx, setup);

    } else if ((setup->request_type & kUsbReqTypeRecipientMask) ==
               kUsbReqTypeInterface) {
      // If its an interface-level request, we handle it here.  These requests
      // will be {Set,Get}Interface.  We use interface altsettings to control
      // which services rescue is communicating with.
      error = interface_request(ctx, setup);
    } else {
      // Otherwise, all other requests get mapped to the standard control
      // endpoint function.
      error = dfu_transport_setupdata(ctx, setup);
      // Take care of the SetConfiguration command.
      if (ctx->ep0.flags & kUsbControlFlagsPendingConfig) {
        ctx->ep0.flags &= ~(unsigned)kUsbControlFlagsPendingConfig;
        error = set_configuration(ctx);
        if (error == kErrorOk) {
          dfu_transport_data(ctx, kUsbDirIn, NULL, 0, 0);
        }
      }
    }
    dfu_transport_result(ctx, error);
  }

  // If we completed a transfer, process the completion.
  if (flags & kUsbTransferFlagsDone) {
    // Take care of the SetAddress command.
    if (ctx->ep0.flags & kUsbControlFlagsPendingAddress) {
      ctx->ep0.flags &= ~(unsigned)kUsbControlFlagsPendingAddress;
      ctx->ep0.device_address = ctx->ep0.next.device_address;
      usb_set_address(ctx->ep0.device_address);
    }

    size_t length = *(size_t *)data;
    if (ctx->dfu_state == kDfuStateDnLoadSync) {
      // If we're in the DnLoadSync state and we completed a transfer, that
      // means the rescue buffer has data to process.
      ctx->state.offset = (uint32_t)length;
      while (ctx->state.offset < sizeof(ctx->state.data)) {
        // Make sure the full buffer is filled.  Fill unused space with 0xFF.
        ctx->state.data[ctx->state.offset++] = 0xFF;
      }
      // Pass the rescue buffer to the rescue receive handler.
      rom_error_t error = rescue_recv_handler(&ctx->state);
      switch (error) {
        case kErrorOk:
          ctx->dfu_error = kDfuErrOk;
          break;
        default:
          ctx->dfu_error = kDfuErrVendor;
      }
      // Back to DnLoadIdle state.
      ctx->dfu_state = kDfuStateDnLoadIdle;
    } else if (ctx->dfu_state == kDfuStateUpLoadIdle) {
      if (length < kDfuTransferSize) {
        ctx->dfu_state = kDfuStateIdle;
      }
      // The amount of staged data is now zero.
      ctx->state.staged_len = 0;
    }
  }

  if (flags & kUsbTransferFlagsReset) {
    // A USB reset after we've been enumerated means software reset.
    if (ctx->ep0.device_address && ctx->ep0.configuration) {
      rstmgr_reboot();
    }
  }

  if (flags & kUsbTransferFlagsError) {
    // If we've been enumerated, then move the DFU state machine into the error
    // state.
    if (ctx->ep0.device_address && ctx->ep0.configuration) {
      ctx->dfu_state = kDfuStateError;
      ctx->dfu_error = kDfuErrUnknown;
    }
  }
}
