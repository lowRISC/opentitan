// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/stdusb.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"

rom_error_t usb_control_setupdata(usb_control_ctx_t *ctx,
                                  usb_setup_data_t *setup) {
  rom_error_t result = kErrorOk;
  uint32_t zero = 0;
  switch (setup->request) {
    case kUsbSetupReqGetDescriptor:
      switch (setup->value >> 8) {
        case kUsbDescTypeDevice:
          usb_ep_transfer(0, (void *)ctx->device_desc,
                          MIN(setup->length, ctx->device_desc->length),
                          kUsbTransferFlagsIn);
          break;
        case kUsbDescTypeConfiguration: {
          usb_configuration_descriptor_t *cfg =
              (usb_configuration_descriptor_t *)ctx->config_desc;
          usb_ep_transfer(0, cfg, MIN(setup->length, cfg->total_length),
                          kUsbTransferFlagsIn);
          break;
        }
        case kUsbDescTypeString: {
          size_t index = setup->value & 0xFF;
          size_t n = 0;
          while (ctx->string_desc[n] != NULL) {
            ++n; /* count number of string descriptor */
          }
          if (index < n) {
            usb_ep_transfer(
                0, (void *)ctx->string_desc[index],
                MIN(setup->length, (uint8_t)ctx->string_desc[index][0]),
                kUsbTransferFlagsIn);
          } else {
            result = kErrorUsbBadSetup;
          }
          break;
        }
        default:
          result = kErrorUsbBadSetup;
      }
      break;

    case kUsbSetupReqSetAddress:
      ctx->next.device_address = (uint8_t)setup->value & 0x7f;
      usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn);
      ctx->flags |= kUsbControlFlagsPendingAddress;
      break;

    case kUsbSetupReqSetConfiguration:
      ctx->next.configuration = (uint8_t)setup->value;
      usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn);
      ctx->flags |= kUsbControlFlagsPendingConfig;
      break;

    case kUsbSetupReqGetConfiguration:
      usb_ep_transfer(0, &ctx->configuration, sizeof(ctx->configuration),
                      kUsbTransferFlagsIn);
      break;

    case kUsbSetupReqSetFeature:
      switch (setup->value) {
        case kUsbFeatureEndpointHalt:
          usb_ep_stall(setup->index, true);
          usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn);
          break;
        default:
          result = kErrorUsbBadSetup;
      }
      break;

    case kUsbSetupReqClearFeature:
      switch (setup->value) {
        case kUsbFeatureEndpointHalt:
          usb_ep_stall(setup->index, false);
          usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn);
          break;
        default:
          result = kErrorUsbBadSetup;
      }
      break;

    case kUsbSetupReqGetStatus: {
      uint8_t type = setup->request_type & kUsbReqTypeRecipientMask;
      uint16_t stat = 0;
      if (type == kUsbReqTypeDevice) {
        stat = kUsbStatusSelfPowered;
      } else if (type == kUsbReqTypeEndpoint) {
        stat = usb_ep_stalled(setup->index) ? kUsbStatusHalted : 0;
      }
      usb_ep_transfer(0, &stat, sizeof(stat), kUsbTransferFlagsIn);
      break;
    }

    case kUsbSetupReqSetInterface:
      // We currently don't support alternate interfaces, so just ignore
      // and send zero length packet for status phase.
      usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn);
      break;

    case kUsbSetupReqGetInterface:
      usb_ep_transfer(0, &zero, 1, kUsbTransferFlagsIn);
      break;

    case kUsbSetupReqSynchFrame:
      usb_ep_transfer(0, &zero, 2, kUsbTransferFlagsIn);
      break;

    default:
      result = kErrorUsbBadSetup;
  }
  return result;
}
