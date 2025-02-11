// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/stdusb.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"

static uint16_t zero;
static uint16_t status;

rom_error_t usb_control_setupdata(usb_control_ctx_t *ctx,
                                  usb_setup_data_t *setup) {
  rom_error_t result = kErrorUsbBadSetup;
  switch (setup->request) {
    case kUsbSetupReqGetDescriptor:
      switch (setup->value >> 8) {
        case kUsbDescTypeDevice:
          return usb_ep_transfer(
              kUsbDirIn | 0, (void *)ctx->device_desc,
              (size_t)MIN(setup->length, ctx->device_desc->length), 0);
        case kUsbDescTypeConfiguration: {
          usb_configuration_descriptor_t *cfg =
              (usb_configuration_descriptor_t *)ctx->config_desc;
          return usb_ep_transfer(kUsbDirIn | 0, cfg,
                                 (size_t)MIN(setup->length, cfg->total_length),
                                 0);
        }
        case kUsbDescTypeString: {
          size_t index = setup->value & 0xFF;
          size_t n = 0;
          while (ctx->string_desc[n] != NULL) {
            ++n; /* count number of string descriptor */
          }
          if (index < n) {
            return usb_ep_transfer(
                kUsbDirIn | 0, (void *)ctx->string_desc[index],
                (size_t)MIN(setup->length, ctx->string_desc[index][0]), 0);
          }
          break;
        }
        default:
            /* nothing */;
      }
      break;

    case kUsbSetupReqSetAddress:
      // Note: You must handle SetAddress in your control endpoint
      // callback after receiving notification that the transfer has
      // completed (e.g. `kUsbTransferFlagsDone`).
      ctx->next.device_address = (uint8_t)setup->value & 0x7f;
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
      ctx->flags |= kUsbControlFlagsPendingAddress;
      return kErrorOk;

    case kUsbSetupReqSetConfiguration:
      // Note: You must handle SetConfiguration in your control endpoint
      // callback after returning from this function.
      // - If you're able to handle the SetConfiguration request without
      //   error, you must ack the transaction with a zero-length packet,
      //   such as: `usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn)
      // - If you're unable to handle the SetConfiguration request,
      //   you must stall: `usb_ep_stall(0)`.
      usb_clear_all_toggles();
      ctx->next.configuration = (uint8_t)setup->value;
      ctx->flags |= kUsbControlFlagsPendingConfig;
      return kErrorOk;

    case kUsbSetupReqGetConfiguration:
      return usb_ep_transfer(kUsbDirIn | 0, &ctx->configuration,
                             sizeof(ctx->configuration), 0);

    case kUsbSetupReqSetFeature:
      switch (setup->value) {
        case kUsbFeatureEndpointHalt:
          RETURN_IF_ERROR(usb_ep_stall((uint8_t)setup->index, true));
          return usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
        default:
            /* nothing */;
      }
      break;

    case kUsbSetupReqClearFeature:
      switch (setup->value) {
        case kUsbFeatureEndpointHalt:
          usb_ep_clear_toggle((uint8_t)setup->index);
          RETURN_IF_ERROR(usb_ep_stall((uint8_t)setup->index, false));
          return usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
        default:
            /* nothing */;
      }
      break;

    case kUsbSetupReqGetStatus: {
      uint8_t type = setup->request_type & kUsbReqTypeRecipientMask;
      if (type == kUsbReqTypeDevice) {
        status = kUsbStatusSelfPowered;
      } else if (type == kUsbReqTypeEndpoint) {
        bool halted;
        usb_ep_stalled((uint8_t)setup->index, &halted);
        status = halted ? kUsbStatusHalted : 0;
      }
      return usb_ep_transfer(kUsbDirIn | 0, &status, sizeof(status), 0);
    }

    case kUsbSetupReqSetInterface:
      // We currently don't support alternate interfaces, so just ignore
      // and send zero length packet for status phase.
      return usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);

    case kUsbSetupReqGetInterface:
      return usb_ep_transfer(kUsbDirIn | 0, &zero, 1, 0);

    case kUsbSetupReqSynchFrame:
      return usb_ep_transfer(kUsbDirIn | 0, &zero, 2, 0);

    default:
        /* nothing */;
  }
  return result;
}
